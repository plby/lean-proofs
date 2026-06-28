import Mathlib
import UnitFractions.Definitions
import UnitFractions.AuxiliaryLemmas
import UnitFractions.Fourier
import UnitFractions.MainResults
import UnitFractions.ForMathlib.BasicEstimates
import UnitFractions.ForMathlib.Misc

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter Finset Real
open _root_.Finset

attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/final_results.lean`.

The main goal here is API coverage: every lemma/theorem from the Lean 3 file has a Lean 4 analog
with a translated statement.
-/

lemma another_weird_tendsto_at_top_aux (c : ℝ) (hc : 1 < c) :
    Tendsto (fun x : ℝ => c ^ x / log x) atTop atTop :=
  ((tendsto_exp_mul_div_rpow_atTop 1 _ (log_pos hc)).atTop_mul_atTop₀
      (tendsto_mul_add_div_pow_log_at_top 1 0 1 zero_lt_one)).congr' <| by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by positivity
    have hlogx : log x ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hx) hx.ne'
    simp [Real.rpow_def_of_pos (lt_trans zero_lt_one hc)]
    field_simp [hx0, hlogx]

lemma the_thing : 1 < exp 2 / 2 := by
  rw [one_lt_div zero_lt_two]
  rw [← Real.log_lt_iff_lt_exp zero_lt_two]
  exact Real.log_two_lt_d9.trans_le (by norm_num)

lemma another_weird_tendsto_at_top :
    Tendsto (fun x : ℝ => x / (2 ^ (1 / 2 * log x + 1) * log (1 / 2 * log x))) atTop atTop := by
  refine (Tendsto.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    ((another_weird_tendsto_at_top_aux (exp 2 / 2) the_thing).comp
      (tendsto_log_atTop.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  rw [Real.div_rpow (show 0 ≤ exp 2 by positivity) zero_le_two, div_div, div_mul_div_comm, one_mul,
    Real.rpow_add_one (show (2 : ℝ) ≠ 0 by norm_num), Real.rpow_def_of_pos (exp_pos 2),
    Real.log_exp, ← mul_assoc, mul_one_div_cancel (show (2 : ℝ) ≠ 0 by norm_num), one_mul,
    Real.exp_log hx, ← mul_assoc, mul_comm (2 : ℝ)]

lemma omega_eq_sum (N : ℕ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    ω n = (((Icc 1 N).filter Nat.Prime).filter fun p => p ∣ n).sum (fun _ => 1) := by
  rw [card_distinct_factors_apply', ← Finset.card_eq_sum_ones]
  have hnIcc := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1)
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, and_assoc]
  constructor
  · intro hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpdvd : p ∣ n := (Nat.mem_primeFactorsList_iff_dvd hn0 hpprime).mp hp
    refine ⟨hpprime.one_lt.le, ?_, hpprime, hpdvd⟩
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd).trans hnIcc.2
  · rintro ⟨_, _, hpprime, hpdvd⟩
    exact (Nat.mem_primeFactorsList_iff_dvd hn0 hpprime).mpr hpdvd

lemma count_multiples'' {m n : ℕ} (hm : 1 ≤ m) :
    (((Icc 1 n).filter fun k => m ∣ k).card : ℝ) = (n / m : ℝ) - Int.fract (n / m : ℝ) := by
  rw [count_multiples hm, Int.self_sub_fract, ← Nat.cast_floor_eq_cast_int_floor,
    Nat.floor_div_eq_div]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma count_multiples''' {m n : ℕ} (hm : 1 ≤ m) :
    (((Icc 1 n).filter fun k => m ∣ k).card : ℝ) ≤ (n / m : ℝ) := by
  rw [count_multiples'' hm, sub_le_self_iff]
  exact Int.fract_nonneg _

lemma sum_prime_counting :
    ∃ C : ℝ,
      Filter.Eventually
        (fun N : ℕ =>
          (N : ℝ) * log (log (N : ℝ)) - C * (N : ℝ) ≤
            (Icc (1 : ℕ) N).sum (fun x => (ω x : ℝ)))
        atTop := by
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).isBigO).bound
  refine ⟨-meissel_mertens + c + 1, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hc] with N hN
  simp only [prime_summatory, Nat.floor_natCast, abs_one, mul_one, norm_eq_abs] at hN
  have hω :
      ∀ x ∈ Icc 1 N, (ω x : ℝ) =
        ((Icc 1 N).filter Nat.Prime).sum (fun p => ite (p ∣ x) (1 : ℝ) 0) := by
    intro x hx
    rw [omega_eq_sum _ hx, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_congr rfl hω, Finset.sum_comm]
  simp only [← Finset.sum_filter]
  have hcount :
      ∀ x ∈ (Icc 1 N).filter Nat.Prime,
        ((Icc 1 N).filter fun a => x ∣ a).sum (fun _ => (1 : ℝ)) =
          (N / x : ℝ) - Int.fract (N / x : ℝ) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [← count_multiples'' hx.1.1, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_congr rfl hcount, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, ← Finset.mul_sum]
  have h₁ :
      (N : ℝ) * (log (log (N : ℝ)) + meissel_mertens - c) ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact sub_le_of_abs_sub_le_left hN
  have h₂ :
      (((Icc 1 N).filter Nat.Prime).sum fun x => Int.fract ((N : ℝ) * (x : ℝ)⁻¹)) ≤ N := by
    refine (sum_le_card_mul_real (A := (Icc 1 N).filter Nat.Prime) (M := 1) ?_).trans ?_
    · intro x hx
      exact (Int.fract_lt_one _).le
    · have hcard : (((Icc 1 N).filter Nat.Prime).card : ℝ) ≤ N := by
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      simpa using hcard
  have hmain :
      (N : ℝ) * (log (log (N : ℝ)) + meissel_mertens - c) - N ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) -
          (((Icc 1 N).filter Nat.Prime).sum fun x => Int.fract ((N : ℝ) * (x : ℝ)⁻¹)) :=
    sub_le_sub h₁ h₂
  convert hmain using 1
  ring

lemma range_eq_insert_Icc {n : ℕ} (hn : 1 ≤ n) : range n = insert 0 (Icc 1 (n - 1)) := by
  ext x
  simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

lemma prime_recip_lazy :
    ∃ c,
      Filter.Eventually
        (fun N : ℕ =>
          ((Icc (1 : ℕ) N).filter Nat.Prime).sum (fun p => (p : ℝ)⁻¹) ≤
            log (log (N : ℝ)) + c)
        atTop := by
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).isBigO).bound
  refine ⟨meissel_mertens + c, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hc] with N hN
  dsimp at hN
  simp only [prime_summatory, Nat.floor_natCast, abs_one, mul_one, abs_sub_le_iff,
    sub_le_iff_le_add', add_assoc] at hN
  exact hN.1

lemma sum_prime_counting_sq :
    ∃ C : ℝ,
      Filter.Eventually
        (fun N : ℕ =>
          (Icc (1 : ℕ) N).sum (fun x => (ω x : ℝ) ^ 2) ≤
            (N : ℝ) * log (log (N : ℝ)) ^ 2 + C * (N : ℝ) * log (log (N : ℝ)))
        atTop := by
  obtain ⟨c, hc⟩ := prime_recip_lazy
  refine ⟨(2 * c + 1) + 1, ?_⟩
  filter_upwards [hc, tendsto_log_log_coe_at_top (eventually_ge_atTop (c ^ 2 + c))] with N hN hN'
  dsimp at hN'
  have hω :
      ∀ x ∈ Icc 1 N, (ω x : ℝ) ^ 2 =
        (((Icc 1 N).filter Nat.Prime).sum (fun p => ite (p ∣ x) (1 : ℝ) 0)) ^ 2 := by
    intro x hx
    rw [omega_eq_sum _ hx, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_congr rfl hω]
  simp_rw [sq, Finset.sum_mul, mul_sum, boole_mul, ← ite_and, @Finset.sum_comm _ _ _ _ (Icc _ _),
    ← sq]
  have hsplit :
      ∀ p ∈ (Icc 1 N).filter Nat.Prime,
        ((Icc 1 N).filter Nat.Prime).sum
            (fun q =>
              (Icc 1 N).sum (fun n => ite (p ∣ n ∧ q ∣ n) (1 : ℝ) 0)) ≤
          (Icc 1 N).sum (fun n => ite (p ∣ n) (1 : ℝ) 0) +
            ((Icc 1 N).filter Nat.Prime).sum
              (fun q => (Icc 1 N).sum (fun n => ite (p * q ∣ n) (1 : ℝ) 0)) := by
    intro p hp
    rw [← Finset.sum_filter_add_sum_filter_not ((Icc 1 N).filter Nat.Prime) (fun q => p = q),
      Finset.sum_filter, Finset.sum_ite_eq, if_pos hp]
    simp only [and_self, add_le_add_iff_left]
    refine (Finset.sum_le_sum ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp hq
      refine Finset.sum_le_sum fun n hn => ?_
      by_cases h : p ∣ n ∧ q ∣ n
      · rw [if_pos h]
        have hpqcop : Nat.Coprime p q := by
          by_contra hcop
          rw [Nat.Prime.not_coprime_iff_dvd] at hcop
          rcases hcop with ⟨r, hr, hrp, hrq⟩
          have hrp' : r = p := (Nat.prime_dvd_prime_iff_eq hr hp.2).mp hrp
          have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq.1.2).mp hrq
          exact hq.2 (hrp'.symm.trans hrq')
        rw [if_pos (hpqcop.mul_dvd_of_dvd_of_dvd h.1 h.2)]
      · rw [if_neg h]
        split_ifs
        · exact zero_le_one
        · rfl
    · intro i hi hif
      simp only [Finset.sum_boole, Nat.cast_nonneg]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole]
  have h₁ :
      (((Icc 1 N).filter Nat.Prime).sum fun x => (((Icc 1 N).filter fun a => x ∣ a).card : ℝ)) ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) := by
    simp only [mul_sum, ← div_eq_mul_inv]
    refine Finset.sum_le_sum fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    exact count_multiples''' hx.1.1
  have h₂ :
      (((Icc 1 N).filter Nat.Prime).sum fun p =>
          (((Icc 1 N).filter Nat.Prime).sum fun q =>
            (((Icc 1 N).filter fun a => p * q ∣ a).card : ℝ))) ≤
        (N : ℝ) * ((((Icc 1 N).filter Nat.Prime).sum fun p => (p : ℝ)⁻¹) ^ 2) := by
    simp only [sq, mul_sum, Finset.sum_mul, ← mul_inv, ← div_eq_mul_inv (N : ℝ), ← Nat.cast_mul]
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp hq
    simpa [Nat.mul_comm] using (count_multiples''' <| Nat.succ_le_of_lt <|
      Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hp.1.1) (lt_of_lt_of_le Nat.zero_lt_one hq.1.1)
    )
  refine (add_le_add h₁ h₂).trans ?_
  set S : ℝ := ((Icc 1 N).filter Nat.Prime).sum fun p => (p : ℝ)⁻¹
  set L : ℝ := log (log (N : ℝ))
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
  have hsq : S ^ 2 ≤ (L + c) ^ 2 := by
    have hSc : S ≤ L + c := by simpa [S, L] using hN
    exact pow_le_pow_left₀ hS0 hSc 2
  have hmain : S + S ^ 2 ≤ L ^ 2 + (((2 * c + 1) + 1) * L) := by
    have hSc : S ≤ L + c := by simpa [S, L] using hN
    nlinarith [hSc, hsq, hN']
  have hmainN := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg N)
  simpa [S, L, left_distrib, right_distrib, mul_assoc, mul_left_comm, mul_comm] using hmainN

lemma count_divisors {x N : ℕ} (hx : x ≠ 0) :
    (((Icc 1 N).filter fun i => x ∣ i).card : ℝ) = (N / x : ℝ) - Int.fract (N / x : ℝ) := by
  simpa using count_multiples'' (m := x) (n := N) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx))

lemma count_divisors' {x N : ℕ} (hx : x ≠ 0) (hN : N ≠ 0) :
    (((range N).filter fun i => x ∣ i).card : ℝ) =
      (N / x : ℝ) - (1 / x - 1 + Int.fract ((N - 1) / x : ℝ)) := by
  have hN' : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
  rw [range_eq_insert_Icc hN', Finset.filter_insert, if_pos (dvd_zero x), card_insert_of_notMem,
    Nat.cast_add_one, count_divisors hx, Nat.cast_sub hN', Nat.cast_one, sub_div]
  · ring
  · simp

lemma is_multiplicative_one {R : Type*} [Ring R] :
    (1 : ArithmeticFunction R).IsMultiplicative := by
  simp only [ArithmeticFunction.isMultiplicative_one]

-- `ite_div` is already available from imported dependencies.

lemma moebius_rec_sum {N : ℕ} (hN : N ≠ 0) :
    N.divisors.sum (fun x => (ArithmeticFunction.moebius x : ℝ) / x) =
      (N.divisors.filter Nat.Prime).prod (fun p => 1 - (p : ℝ)⁻¹) := by
  let f' : ArithmeticFunction ℝ := ⟨fun x => (ArithmeticFunction.moebius x : ℝ) / x, by simp⟩
  have hf' : f'.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f']
    · intro m n hmn
      simp [f', ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
        mul_div_mul_comm, Nat.cast_mul, Int.cast_mul]
  let f : ArithmeticFunction ℝ := f' * ArithmeticFunction.zeta
  have hf : f.IsMultiplicative := hf'.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  change ∑ x ∈ N.divisors, f' x = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  change f N = _
  rw [← Nat.primeFactors_eq_to_filter_divisors_prime]
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
        Finset.sum_range_succ', Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
      simp [f', ArithmeticFunction.moebius_apply_prime_pow, hp, hk, ite_div]
      ring
  | zero =>
      cases hN rfl
  | one =>
      simp [hf.map_one]
  | coprime a b ha hb hab aih bih =>
      have ha0 : a ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ha)
      have hb0 : b ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb)
      rw [hf.map_mul_of_coprime hab, Nat.primeFactors_mul ha0 hb0, Finset.prod_union]
      · rw [aih ha0, bih hb0]
      · exact hab.disjoint_primeFactors

lemma prod_sdiff'' {ι α : Type*} [DecidableEq ι] [CommGroupWithZero α] (f : ι → α)
    (s t : Finset ι)
    (h : t ⊆ s) (ht : ∀ i ∈ t, f i ≠ 0) :
    (s \ t).prod f = s.prod f / t.prod f := by
  rw [eq_div_iff_mul_eq]
  · rw [Finset.prod_sdiff h]
  · exact Finset.prod_ne_zero_iff.mpr fun i hi => ht i hi

lemma filter_sdiff {ι : Type*} (p : ι → Prop) [DecidableEq ι] [DecidablePred p]
    (s t : Finset ι) :
    (s \ t).filter p = s.filter p \ t.filter p := by
  ext x
  by_cases hs : x ∈ s
  all_goals
    by_cases ht : x ∈ t
  all_goals
    by_cases hp : p x
  all_goals
    simp [hs, ht, hp, Finset.mem_sdiff, Finset.mem_filter]

lemma product_of_primes_factors {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    (s.prod id).primeFactorsList = s.sort (fun a b => a ≤ b) := by
  refine
    ((Nat.primeFactorsList_unique (n := s.prod id)
        (l := s.sort (fun a b => a ≤ b)) ?_ ?_).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  · calc
      (s.sort (fun a b => a ≤ b)).prod = (s.sort (fun a b => a ≤ b)).toFinset.prod id := by
          simpa using (List.prod_toFinset id (s.sort_nodup (fun a b => a ≤ b))).symm
      _ = s.prod id := by rw [Finset.sort_toFinset]
  · intro p hp
    exact hs p ((Finset.mem_sort (fun a b => a ≤ b)).mp hp)
  · exact pairwise_sort _ _

lemma product_of_primes_factors_to_finset {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    (s.prod id).primeFactorsList.toFinset = s := by
  rw [product_of_primes_factors hs, Finset.sort_toFinset]

lemma mem_factors_prod {A : Finset ℕ} (h : ∀ n ∈ A, n ≠ 0) {p : ℕ} :
    p ∈ (A.prod id).primeFactorsList ↔ ∃ a ∈ A, p ∈ (a : ℕ).primeFactorsList := by
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert n A hnA ih =>
      have hn0 : n ≠ 0 := h n (Finset.mem_insert_self _ _)
      have hA : ∀ m ∈ A, m ≠ 0 := by
        intro m hm
        exact h m (Finset.mem_insert_of_mem hm)
      have hprod0 : A.prod id ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro m hm
        exact hA m hm
      rw [Finset.prod_insert hnA]
      change p ∈ (n * A.prod id).primeFactorsList ↔ ∃ a ∈ insert n A, p ∈ (a : ℕ).primeFactorsList
      rw [Nat.mem_primeFactorsList_mul hn0 hprod0]
      constructor
      · intro hp
        rcases hp with hp | hp
        · exact ⟨n, Finset.mem_insert_self _ _, hp⟩
        · rw [ih hA] at hp
          rcases hp with ⟨a, ha, hpa⟩
          exact ⟨a, Finset.mem_insert_of_mem ha, hpa⟩
      · rintro ⟨a, ha, hpa⟩
        rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inl hpa
        · exact Or.inr ((ih hA).2 ⟨a, ha, hpa⟩)

lemma prod_primes_squarefree {A : Finset ℕ} (h : ∀ n ∈ A, Nat.Prime n) :
    Squarefree (A.prod id) := by
  exact squarefree_prime_prod id h (fun _ _ _ _ hEq => hEq)

lemma sieve_lemma_prec (N : ℕ) (y z : ℝ) (hy : 1 ≤ y) (hzN : z < N) :
    ((((range N).filter
          fun n =>
            ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ)) ≤
      (partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊) * N + 2 ^ (z + 1) := by
  by_cases hN0 : N = 0
  · rw [hN0, Finset.range_zero, Finset.filter_empty]
    norm_num
    exact Real.rpow_nonneg zero_le_two _
  rcases lt_or_ge z y with h | h
  · calc
      (((range N).filter
            fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ) ≤ (N : ℝ) := by
          have hcard :
              ((range N).filter
                    fun n =>
                      ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card ≤
                (range N).card :=
            Finset.card_filter_le _ _
          simpa using hcard
      _ ≤ (partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊) * N + 2 ^ (z + 1) := by
          rw [← add_zero (N : ℝ)]
          refine add_le_add ?_ ?_
          · rw [add_zero]
            refine le_mul_of_one_le_left (Nat.cast_nonneg N) ?_
            rw [one_le_div]
            · rw [partial_euler_product, partial_euler_product]
              refine prod_of_subset_le_prod_of_one_le ?_ ?_ ?_
              · intro p hp
                rw [Finset.mem_filter, Finset.mem_Icc]
                rw [Finset.mem_filter, Finset.mem_Icc] at hp
                refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
                exact le_trans hp.1.2 (Nat.floor_mono h.le)
              · intro p hp
                rw [inv_nonneg]
                rw [Finset.mem_filter] at hp
                have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
                exact sub_nonneg.mpr (le_of_lt (inv_lt_one_of_one_lt₀ hp1))
              · intro p hp1 hp2
                rw [Finset.mem_filter] at hp1
                have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1.2.one_lt
                have hpos : 0 < 1 - (p : ℝ)⁻¹ :=
                  sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1')
                refine (one_le_inv₀ hpos).2 ?_
                exact sub_le_self _ (inv_nonneg.2 (Nat.cast_nonneg p))
            · exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
          · exact Real.rpow_nonneg zero_le_two _
  · let P :=
      ((range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z).prod id
    have hP : P ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      exact hx.2.1.pos.ne'
    have h₁ :
        ((range N).filter fun n =>
            ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card =
          ((range N).filter fun n => Nat.Coprime n P).card := by
      congr 1
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn, hn'⟩
        refine ⟨hn, ?_⟩
        rw [Nat.coprime_prod]
        intro p hpP
        have hp : Nat.Prime p := (Finset.mem_filter.mp hpP).2.1
        have hy' : y ≤ p := (Finset.mem_filter.mp hpP).2.2.1
        have hz' : (p : ℝ) ≤ z := (Finset.mem_filter.mp hpP).2.2.2
        change Nat.Coprime n p
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro hdiv
        cases hn' p hp hdiv with
        | inl hlt => exact (not_lt_of_ge hy') hlt
        | inr hgt => exact (not_lt_of_ge hz') hgt
      · rintro ⟨hn, hn'⟩
        refine ⟨hn, ?_⟩
        intro p hp hpdvd
        by_contra hbad
        push Not at hbad
        have hpRange : p ∈ range N := by
          rw [Finset.mem_range]
          exact_mod_cast (lt_of_le_of_lt hbad.2 hzN)
        have hpP : p ∈ (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z := by
          simp [hpRange, hp, hbad.1, hbad.2]
        have hnotcop : ¬ Nat.Coprime n p := by
          have hnotcop' : ¬ Nat.Coprime p n := by
            rw [hp.coprime_iff_not_dvd]
            exact not_not_intro hpdvd
          simpa [Nat.coprime_comm] using hnotcop'
        rw [Nat.coprime_prod] at hn'
        exact hnotcop (hn' p hpP)
    have hmu :
        ∀ n, ∑ i ∈ (Nat.gcd n P).divisors, (ArithmeticFunction.moebius i : ℝ) =
          ite (Nat.gcd n P = 1) 1 0 := by
      intro n
      rw [← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.moebius_mul_coe_zeta]
      change ((ite ((Nat.gcd n P) = 1) 1 0 : ℤ) : ℝ) = _
      split_ifs
      · simp
      · simp
    rw [h₁, ← Finset.sum_boole]
    simp only [Nat.Coprime]
    simp_rw [← hmu]
    have hgcddiv : ∀ x : ℕ, (Nat.gcd x P).divisors = P.divisors.filter fun d => d ∣ x := by
      intro x
      ext m
      constructor
      · intro hm
        rw [Nat.mem_divisors] at hm
        rcases (Nat.dvd_gcd_iff.mp hm.1) with ⟨hmx, hmP⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hmP, hP⟩, hmx⟩
      · intro hm
        rw [Finset.mem_filter, Nat.mem_divisors] at hm
        rcases hm with ⟨⟨hmP, hP'⟩, hmx⟩
        rw [Nat.mem_divisors]
        refine ⟨Nat.dvd_gcd hmx hmP, ?_⟩
        intro hgcd0
        have h0dvd : 0 ∣ P := by
          simpa [hgcd0] using (Nat.gcd_dvd_right x P)
        exact hP' (by simpa using h0dvd)
    simp_rw [hgcddiv, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [← mul_boole _ (ArithmeticFunction.moebius _ : ℝ), ← Finset.mul_sum]
    simp_rw [Finset.sum_boole]
    have hcount :
        ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) *
            ((((range N).filter fun i => x ∣ i).card : ℝ)) =
          ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) *
            ((N / x : ℝ) - (1 / x - 1 + Int.fract ((N - 1) / x : ℝ))) := by
      rw [Finset.sum_congr rfl]
      intro x hx
      rw [count_divisors']
      · rw [Nat.mem_divisors] at hx
        exact ne_zero_of_dvd_ne_zero hx.2 hx.1
      · exact hN0
    simp_rw [hcount, mul_sub]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_div_assoc', mul_comm _ (N : ℝ), mul_div_assoc]
    rw [← Finset.mul_sum]
    have hP_divisors :
        P.divisors.filter Nat.Prime =
          (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z := by
      rw [← Nat.primeFactors_eq_to_filter_divisors_prime]
      change (((range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z).prod id).primeFactors =
        (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z
      rw [Nat.primeFactors]
      exact
        product_of_primes_factors_to_finset
          (s := (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z)
          (by
            intro p hp
            exact (Finset.mem_filter.mp hp).2.1)
    have hP_divisors' :
        (Icc 1 ⌊z⌋₊ \ Icc 1 ⌊y⌋₊).filter Nat.Prime ⊆ P.divisors.filter Nat.Prime := by
      rw [hP_divisors, Icc_sdiff_Icc_left (Nat.floor_mono h) ((Nat.one_le_floor_iff y).2 hy)]
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hprime : Nat.Prime n := hn.2
      have hylt : y < n := (Nat.floor_lt' hprime.ne_zero).1 hn.1.1
      have hz0 : 0 ≤ z := zero_le_one.trans (le_trans hy h)
      have hnz : (n : ℝ) ≤ z := (Nat.le_floor_iff hz0).1 hn.1.2
      have hnN : n < N := by
        exact_mod_cast (lt_of_le_of_lt hnz hzN)
      simpa [Finset.mem_filter] using ⟨hnN, hprime, hylt.le, hnz⟩
    have hPsum :
        ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) / x ≤
          partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ := by
      rw [moebius_rec_sum hP, partial_euler_product, partial_euler_product, Finset.prod_inv_distrib,
        Finset.prod_inv_distrib, inv_div_inv, ← prod_sdiff'', ← filter_sdiff]
      · refine Finset.prod_le_prod_of_subset_of_le_one ?_ ?_ ?_
        · convert hP_divisors'
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
          exact sub_nonneg.mpr (le_of_lt (inv_lt_one_of_one_lt₀ hp1))
        · intro p hp1 hp2
          refine sub_le_self _ ?_
          rw [inv_nonneg]
          exact Nat.cast_nonneg p
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
        exact le_trans hp.1.2 (Nat.floor_mono h)
      · intro p hp
        refine ne_of_gt ?_
        rw [Finset.mem_filter] at hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
        exact sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
    rw [sub_eq_add_neg]
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left hPsum (Nat.cast_nonneg N)
    · refine le_trans (le_abs_self _) ?_
      rw [abs_neg]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc
        ∑ x ∈ P.divisors,
            |(ArithmeticFunction.moebius x : ℝ) *
              (1 / x - 1 + Int.fract ((N - 1) / x : ℝ))| ≤
            (2 : ℝ) * (ArithmeticFunction.sigma 0 P : ℝ) := by
              rw [ArithmeticFunction.sigma_zero_apply]
              refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans ?_
              · intro d hd
                rw [abs_mul, ← one_mul (2 : ℝ)]
                refine mul_le_mul ?_ ?_ ?_ ?_
                · by_cases hdsq : Squarefree d
                  · rw [ArithmeticFunction.moebius_apply_of_squarefree hdsq]
                    norm_num
                  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
                    norm_num
                · rw [← add_sub_right_comm, ← add_sub]
                  refine le_trans (abs_add_le _ _) ?_
                  transitivity (1 : ℝ) + 1
                  · refine add_le_add ?_ ?_
                    · rw [abs_of_nonneg]
                      · have hd1 : (1 : ℝ) ≤ d := by
                          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hd)
                        simpa [one_div] using
                          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hd1)
                      · rw [one_div_nonneg]
                        exact Nat.cast_nonneg d
                    · rw [abs_of_nonpos, neg_sub]
                      · exact sub_le_self _ (Int.fract_nonneg _)
                      · rw [sub_nonpos]
                        exact le_of_lt (Int.fract_lt_one _)
                  · norm_num
                · exact abs_nonneg _
                · exact zero_le_one
              · simp only [nsmul_eq_mul]
                rw [mul_comm]
        _ ≤ 2 ^ (z + 1) := by
          have hPsq : Squarefree P := by
            refine prod_primes_squarefree ?_
            intro p hp
            rw [Finset.mem_filter] at hp
            exact hp.2.1
          rw [divisor_count_eq_pow_iff_squarefree.2 hPsq, Nat.cast_pow]
          norm_num
          rw [← Real.rpow_natCast, mul_comm, ← Real.rpow_add_one]
          · refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
            rw [card_distinct_factors_apply']
            transitivity (((insert 0 P.primeFactorsList.toFinset).card : ℕ) : ℝ)
            · rw [Finset.card_insert_of_notMem]
              · norm_num
              · rw [List.mem_toFinset]
                intro hbad
                exact Nat.not_prime_zero (Nat.prime_of_mem_primeFactorsList hbad)
            · transitivity (((Icc 0 ⌊z⌋₊).card : ℕ) : ℝ)
              · have hsubset : insert 0 P.primeFactorsList.toFinset ⊆ Icc 0 ⌊z⌋₊ := by
                  intro p hp
                  rw [Finset.mem_insert] at hp
                  rcases hp with rfl | hp
                  · simp only [Finset.left_mem_Icc, Nat.zero_le]
                  · rw [List.mem_toFinset,
                      mem_factors_prod
                        (h := by
                          intro n hn
                          exact Nat.Prime.ne_zero (Finset.mem_filter.mp hn).2.1)] at hp
                    rcases hp with ⟨q, hq1, hq2⟩
                    rw [Finset.mem_filter] at hq1
                    rw [Nat.primeFactorsList_prime hq1.2.1, List.mem_singleton] at hq2
                    rw [hq2, Finset.mem_Icc]
                    refine ⟨Nat.zero_le q, ?_⟩
                    exact (Nat.le_floor_iff (zero_le_one.trans (le_trans hy h))).2 hq1.2.2.2
                exact_mod_cast (Finset.card_le_card hsubset)
              · rw [Nat.card_Icc, Nat.cast_sub]
                · push_cast
                  rw [sub_zero]
                  nlinarith [Nat.floor_le (zero_le_one.trans (le_trans hy h))]
                · exact Nat.zero_le (⌊z⌋₊ + 1)
          · norm_num

lemma sieve_lemma_prec' :
    ∃ C c : ℝ,
      0 < C ∧
        0 < c ∧
          Filter.Eventually
            (fun N : ℕ =>
              ∀ y z : ℝ,
                2 ≤ y →
                  1 < z →
                    z ≤ c * log (N : ℝ) →
                      ((((range N).filter fun n =>
                              ∀ p : ℕ,
                                Nat.Prime p →
                                  p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ)) ≤
                        C * (log y / log z) * N)
            atTop := by
  rcases weak_mertens_third_lower_all with ⟨C₁, hC₁, hml⟩
  rcases weak_mertens_third_upper_all with ⟨C₂, hC₂, hmu⟩
  let C := 1 / C₁ * C₂ * 2
  let c : ℝ := 1 / 2
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos ?_ zero_lt_two
    refine mul_pos ?_ hC₂
    exact one_div_pos.mpr hC₁
  refine ⟨C, c, h0C, by norm_num, ?_⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (2 : ℝ))
    , (another_weird_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 / (C / 2 * log 2))) ] with
      N h0N hlogN hweirdN
  dsimp at hlogN hweirdN
  intro y z h2y h1z hzN
  have h0logN : 0 < log (N : ℝ) := by
    linarith
  have hzNhalf : z ≤ 1 / 2 * log (N : ℝ) := by
    simpa [c] using hzN
  have hzN' : z < N := by
    have hcLog : c * log (N : ℝ) ≤ log (N : ℝ) := by
      dsimp [c]
      refine mul_le_of_le_one_left h0logN.le ?_
      change (1 : ℝ) / 2 ≤ 1
      exact half_le_self zero_le_one
    exact hzN.trans_lt (lt_of_le_of_lt hcLog (log_lt_self h0N))
  refine le_trans (sieve_lemma_prec N y z (le_trans (by norm_num) h2y) hzN') ?_
  rw [← add_halves C, add_mul, add_mul]
  refine add_le_add ?_ ?_
  · have hlogz : 0 < log z := Real.log_pos h1z
    have hpepz_pos : 0 < partial_euler_product ⌊z⌋₊ := by
      exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
    have hmu' : partial_euler_product ⌊y⌋₊ ≤ C₂ * log y := by
      have hmu0 := hmu y h2y
      have hpepy_pos : 0 < partial_euler_product ⌊y⌋₊ := by
        exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
      simpa [Real.norm_eq_abs, abs_of_pos hpepy_pos,
        abs_of_pos (Real.log_pos (lt_of_lt_of_le one_lt_two h2y))] using hmu0
    have hml' : C₁ * log z ≤ partial_euler_product ⌊z⌋₊ := by
      have hml0 := hml z (le_of_lt h1z)
      simpa [Real.norm_eq_abs, abs_of_pos hlogz,
        abs_of_pos hpepz_pos] using hml0
    have hC : C / 2 = (1 / C₁) * C₂ := by
      dsimp [C]
      ring
    have hbase' :
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
          (((1 / C₁) * C₂) * log y) / log z := by
      refine (div_le_div_iff₀ hpepz_pos hlogz).2 ?_
      transitivity C₂ * log y * log z
      · exact mul_le_mul_of_nonneg_right hmu' hlogz.le
      · have hylog_nonneg : 0 ≤ log y := Real.log_nonneg (le_trans one_le_two h2y)
        have hcoeff_nonneg : 0 ≤ C₂ * log y / C₁ := by
          rw [div_eq_mul_inv]
          exact mul_nonneg (mul_nonneg hC₂.le hylog_nonneg) (inv_nonneg.2 hC₁.le)
        have hstep :
            (C₂ * log y / C₁) * (C₁ * log z) ≤
              (C₂ * log y / C₁) * partial_euler_product ⌊z⌋₊ := by
          exact mul_le_mul_of_nonneg_left hml' hcoeff_nonneg
        calc
          C₂ * log y * log z = (C₂ * log y / C₁) * (C₁ * log z) := by
            field_simp [hC₁.ne']
          _ ≤ (C₂ * log y / C₁) * partial_euler_product ⌊z⌋₊ := hstep
          _ = (((1 / C₁) * C₂) * log y) * partial_euler_product ⌊z⌋₊ := by
            ring
    have hbase :
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
          (C / 2) * (log y / log z) := by
      calc
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
            (((1 / C₁) * C₂) * log y) / log z := hbase'
        _ = (C / 2) * (log y / log z) := by
          rw [hC]
          ring
    exact mul_le_mul_of_nonneg_right hbase h0N.le
  · have hlogz : 0 < log z := Real.log_pos h1z
    have hmainpow :
        2 ^ (z + 1) ≤ (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) := by
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      linarith
    have hloghalf :
        log z ≤ log (1 / 2 * log (N : ℝ)) := by
      refine Real.log_le_log (lt_trans zero_lt_one h1z) hzNhalf
    have hhalfpos : 0 < log (1 / 2 * log (N : ℝ)) := by
      have hhalfgt1 : 1 < 1 / 2 * log (N : ℝ) := by
        linarith
      refine Real.log_pos ?_
      exact hhalfgt1
    have hweird' :
        (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ)) ≤
          (C / 2 * log 2) * N := by
      have hApos : 0 < C / 2 * log 2 := by
        refine mul_pos ?_ (Real.log_pos one_lt_two)
        exact div_pos h0C zero_lt_two
      have hBpos :
          0 < (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ)) := by
        refine mul_pos (Real.rpow_pos_of_pos zero_lt_two _) hhalfpos
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (div_le_div_iff₀ hApos hBpos).1 hweirdN
    transitivity (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1)
    · exact hmainpow
    transitivity
      ((2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ))) / log z
    · rw [le_div_iff₀ hlogz]
      exact mul_le_mul_of_nonneg_left hloghalf
        (Real.rpow_nonneg (by positivity) _)
    · transitivity ((C / 2 * log 2) * N) / log z
      · exact div_le_div_of_nonneg_right hweird' hlogz.le
      · have hylog2 : log 2 ≤ log y := Real.log_le_log zero_lt_two h2y
        have hnum :
            (C / 2 * log 2) * N ≤ (C / 2 * log y) * N := by
          gcongr
        exact (div_le_div_of_nonneg_right hnum hlogz.le).trans_eq (by ring)

lemma plogp_tail_bound (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ N in (atTop : Filter ℕ),
          ∀ z : ℝ,
            0 ≤ log (log ⌊z⌋₊) →
              ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
                c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
  obtain ⟨c₁, hmertens⟩ := Filter.eventually_atTop.mp explicit_mertens
  let c : ℝ := a * 2
  refine ⟨c, mul_pos ha zero_lt_two, ?_⟩
  filter_upwards [eventually_gt_atTop 4, eventually_ge_atTop c₁] with N h4N hcN
  have h0Nnat : 0 < N := by omega
  have h0N : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h0Nnat
  have hlogN : 0 < log ((N : ℝ) / 4) := by
    refine Real.log_pos ?_
    rw [one_lt_div zero_lt_four]
    exact_mod_cast h4N
  intro z hz'
  by_cases hz : (N : ℝ) ≤ z
  · have hNz : N ≤ ⌊z⌋₊ := by
      rw [Nat.le_floor_iff' (Nat.ne_of_gt h0Nnat)]
      exact hz
    calc
      ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
          ((Icc N ⌊z⌋₊).filter Nat.Prime).sum
            (fun x => (a / log ((N : ℝ) / 4)) * (1 / x : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
        rcases Finset.mem_Icc.mp hpIcc with ⟨hpN, hpz⟩
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpN
        have hlogp : 0 < log ((p : ℝ) / 4) := by
          refine Real.log_pos ?_
          rw [one_lt_div zero_lt_four]
          exact_mod_cast lt_of_lt_of_le h4N hpN
        have hlogNp : log ((N : ℝ) / 4) ≤ log ((p : ℝ) / 4) := by
          refine Real.log_le_log (div_pos h0N zero_lt_four) ?_
          exact div_le_div_of_nonneg_right hNp zero_lt_four.le
        have hrecip :
            1 / log ((p : ℝ) / 4) ≤ 1 / log ((N : ℝ) / 4) :=
          one_div_le_one_div_of_le hlogN hlogNp
        have hdiv :=
          mul_le_mul_of_nonneg_left hrecip (div_nonneg ha.le hp0.le)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = (a / log ((N : ℝ) / 4)) *
            (((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => (1 / x : ℝ))) := by
        rw [← Finset.mul_sum]
      _ ≤ (a / log ((N : ℝ) / 4)) *
            ((((range (⌊z⌋₊ + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqPrime⟩
          rcases Finset.mem_Icc.mp hqIcc with ⟨_, hqz⟩
          exact
            Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqz), hqPrime.isPrimePow⟩
        · intro n _ _
          exact one_div_nonneg.2 (Nat.cast_nonneg n)
      _ ≤ (a / log ((N : ℝ) / 4)) * (2 * log (log ⌊z⌋₊)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        exact hmertens ⌊z⌋₊ (le_trans hcN hNz)
      _ = c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
        dsimp [c]
        ring
  · have hIcc : Icc N ⌊z⌋₊ = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact (Nat.floor_lt' (Nat.ne_of_gt h0Nnat)).2 (lt_of_not_ge hz)
    rw [hIcc, Finset.filter_empty, Finset.sum_empty]
    refine div_nonneg ?_ hlogN.le
    exact mul_nonneg (by
      dsimp [c]
      positivity) hz'

lemma filter_div_aux (a b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∃ y z w : ℝ,
      2 ≤ y ∧
        16 ≤ w ∧
          0 < z ∧
            1 < z ∧
              4 * y + 4 ≤ z ∧
                a ≤ y ∧
                  d ≤ y ∧
                    log w / log z ≤ b ∧
                      ((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
                          (fun x => log y / (log (x / 4) * x)) ≤
                        c := by
  let y : ℝ := max 2 (max a d)
  have hlogy : 0 < log y := by
    refine Real.log_pos ?_
    exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
  obtain ⟨C₁, h0C₁, htail⟩ := plogp_tail_bound (log y) hlogy
  rw [Filter.eventually_atTop] at htail
  obtain ⟨C₂', htail'⟩ := htail
  let C₂ : ℝ := max 1 C₂'
  let ε : ℝ := c * b / (2 * C₁)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have haux := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound hε
  have haux' := Real.tendsto_log_atTop.eventually haux
  rw [Filter.eventually_atTop] at haux'
  obtain ⟨C₃, haux'⟩ := haux'
  let z : ℝ :=
    max (exp (log 4 * 2 / b))
      (max C₃
        (max 3
          (max (4 * y + 4)
            (max (exp (exp (log (16 / 4) * c / C₁)) + 1)
              (exp (exp (log (C₂ / 4) * c / C₁)) + 1)))))
  let w : ℝ := 4 * exp (C₁ * log (log ⌊z⌋₊) / c)
  have hz₁ : exp (log 4 * 2 / b) ≤ z := by
    exact le_max_left _ _
  have hz₂ : C₃ ≤ z := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hz₄' : 3 ≤ z := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hz₄ : 2 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    norm_num
  have hz₅ : exp 1 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hz₆ : 4 * y + 4 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hzfloor : z - 1 ≤ ⌊z⌋₊ := by
    rw [sub_le_iff_le_add]
    exact le_of_lt (Nat.lt_floor_add_one _)
  have hz₃ : 1 ≤ z := le_trans one_le_two (le_of_lt hz₄)
  have hz₀ : 0 < z := lt_of_lt_of_le zero_lt_one hz₃
  have hz₈' : exp (exp (log (16 / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₉' : exp (exp (log (C₂ / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₈ : log (16 / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₈'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₉ : log (C₂ / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₉'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₇ : 0 ≤ log (log ⌊z⌋₊) := by
    refine le_trans ?_ hz₈
    refine div_nonneg ?_ h0C₁.le
    refine mul_nonneg ?_ hc.le
    exact Real.log_nonneg (by norm_num)
  have hzw : exp (log w / b) ≤ z := by
    have hlogz : 0 < log z := Real.log_pos (lt_trans one_lt_two hz₄)
    have hloglogz : log (log z) ≤ ε * log z := by
      specialize haux' z hz₂
      have hloglogz_pos : 0 < log (log z) := by
        refine Real.log_pos ?_
        rw [← Real.exp_lt_exp, Real.exp_log hz₀]
        exact hz₅
      rw [Real.norm_eq_abs, abs_of_pos hloglogz_pos, Real.rpow_one, Real.norm_eq_abs,
        abs_of_pos hlogz] at haux'
      exact haux'
    have hlogfloor_pos : 0 < log ⌊z⌋₊ := by
      refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      linarith
    have hloglogfloor_le : log (log ⌊z⌋₊) ≤ log (log z) := by
      refine Real.log_le_log hlogfloor_pos ?_
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.floor_pos.mpr hz₃
      · exact_mod_cast Nat.floor_le hz₀.le
    have hfirst' : log 4 * 2 / b ≤ log z := by
      rw [← Real.exp_le_exp, Real.exp_log hz₀]
      exact hz₁
    have hfirst : log 4 / b ≤ log z / 2 := by
      have hfirst'' : (log 4 * 2 / b) / 2 ≤ log z / 2 := by
        exact div_le_div_of_nonneg_right hfirst' zero_le_two
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfirst''
    have hsecond' : log (log ⌊z⌋₊) ≤ ε * log z := by
      exact le_trans hloglogfloor_le hloglogz
    have hsecond :
        C₁ * log (log ⌊z⌋₊) / c / b ≤ log z / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hsecond' (show 0 ≤ C₁ / c / b by positivity)
      calc
        C₁ * log (log ⌊z⌋₊) / c / b = (C₁ / c / b) * log (log ⌊z⌋₊) := by ring
        _ ≤ (C₁ / c / b) * (ε * log z) := by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = log z / 2 := by
          dsimp [ε]
          field_simp [h0C₁.ne', hc.ne', hb.ne']
    have hlogw :
        log w / b ≤ log z := by
      rw [show log w = log 4 + C₁ * log (log ⌊z⌋₊) / c by
          rw [show w = 4 * exp (C₁ * log (log ⌊z⌋₊) / c) by rfl,
            Real.log_mul zero_lt_four.ne' (Real.exp_ne_zero _), Real.log_exp],
        add_div]
      have hsum : log 4 / b + (C₁ * log (log ⌊z⌋₊) / c) / b ≤ log z / 2 + log z / 2 := by
        exact add_le_add hfirst hsecond
      simpa [add_halves] using hsum
    rw [← Real.exp_log hz₀]
    exact Real.exp_le_exp.mpr hlogw
  have h16w : 16 ≤ w := by
    have hmain : log (16 / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₈ (show 0 ≤ C₁ / c by positivity)
      calc
        log (16 / 4) = (C₁ / c) * (log (16 / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : (16 : ℝ) / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (by norm_num : 0 < (16 : ℝ) / 4)] using Real.exp_le_exp.mpr hmain
    calc
      (16 : ℝ) = 4 * ((16 : ℝ) / 4) := by norm_num
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have hC₂w : C₂ ≤ w := by
    have hC₂ : (0 : ℝ) < C₂ := by
      dsimp [C₂]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hmain : log (C₂ / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₉ (show 0 ≤ C₁ / c by positivity)
      calc
        log (C₂ / 4) = (C₁ / c) * (log (C₂ / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : C₂ / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (div_pos hC₂ zero_lt_four)] using Real.exp_le_exp.mpr hmain
    calc
      C₂ = 4 * (C₂ / 4) := by field_simp [zero_lt_four.ne']
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have h0w' : (1 : ℝ) < ⌈w⌉₊ / 4 := by
    rw [lt_div_iff₀ zero_lt_four]
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    refine lt_of_lt_of_le ?_ h16w
    norm_num
  refine ⟨y, z, w, le_max_left _ _, h16w, hz₀, lt_trans one_lt_two hz₄, hz₆,
    le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_, ?_⟩
  · have hlogwz : log w / b ≤ log z := by
      have htmp : exp (log w / b) ≤ exp (log z) := by
        simpa [Real.exp_log hz₀] using hzw
      exact Real.exp_le_exp.mp htmp
    refine (div_le_iff₀ (Real.log_pos (lt_trans one_lt_two hz₄))).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hb).mp hlogwz
  · have h₁ : C₂' ≤ ⌈w⌉₊ := by
      have h₁r : (C₂' : ℝ) ≤ ⌈w⌉₊ := by
        exact le_trans (le_max_right _ _) (le_trans hC₂w (Nat.le_ceil w))
      exact_mod_cast h₁r
    refine le_trans (htail' ⌈w⌉₊ h₁ z hz₇) ?_
    have hlogceil : C₁ * log (log ⌊z⌋₊) / c ≤ log (⌈w⌉₊ / 4) := by
      rw [← Real.exp_le_exp, Real.exp_log (lt_trans zero_lt_one h0w')]
      calc
        exp (C₁ * log (log ⌊z⌋₊) / c) = w / 4 := by
          dsimp [w]
          field_simp
        _ ≤ ⌈w⌉₊ / 4 := by
          exact div_le_div_of_nonneg_right (Nat.le_ceil w) zero_le_four
    have hnum : C₁ * log (log ⌊z⌋₊) / log (⌈w⌉₊ / 4) ≤ c := by
      refine (div_le_iff₀ (Real.log_pos h0w')).2 ?_
      have hmul := mul_le_mul_of_nonneg_left hlogceil hc.le
      calc
        C₁ * log (log ⌊z⌋₊) = c * (C₁ * log (log ⌊z⌋₊) / c) := by
          field_simp [hc.ne']
        _ ≤ c * log (⌈w⌉₊ / 4) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hnum

lemma filter_div (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            2 / (1 / (5 * D * 2) * D) ≤ y ∧
              2 / (1 / (5 * D * 2)) ≤ y ∧
                ∀ᶠ N in (atTop : Filter ℕ),
                  ∀ A ⊆ range N,
                    ((A.filter fun n =>
                          ¬ ∃ d₁ d₂ : ℕ,
                              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                      ℝ) ≤
                      (N : ℝ) / (5 * D) := by
  rcases sieve_lemma_prec' with ⟨C, c, h0C, h0c, hsieve⟩
  have haux1 : 0 < (1 / (10 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  have haux2 : 0 < (1 / (20 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  rw [Filter.eventually_atTop] at hsieve
  rcases hsieve with ⟨T, hsieve⟩
  rcases
      (filter_div_aux (2 / (1 / (5 * D * 2) * D)) ((1 / (10 * D)) / C) ((1 / (20 * D)) / C)
          (2 / (1 / (5 * D * 2))) haux1 haux2) with
    ⟨y, z, w, h2y, h16w, h0z, h1z, hyz, hDy, hDy', hwzD', hzsum⟩
  have hwzD : C * (log w / log z) ≤ 1 / (10 * D) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_div_iff₀ h0C).mp hwzD'
  have h2w : 2 ≤ w := by
    refine le_trans ?_ h16w
    norm_num
  have h1y : 1 ≤ y := le_trans one_le_two h2y
  have h0zc : (0 : ℝ) < ⌊z⌋₊ := by
    exact_mod_cast Nat.floor_pos.mpr (le_of_lt h1z)
  refine ⟨y, z, h1y, hyz, h0z, hDy, hDy', ?_⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((T : ℝ) * ⌊z⌋₊))
    , tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop
          ((((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
              (fun x => C * (log y / log (x / 4) * 1))) *
            (20 * D)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((4 : ℝ) * ⌊z⌋₊ / c + log ⌊z⌋₊))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (z / c))
    , eventually_ge_atTop T ] with N h0N hTzN hweirdN hlogN1 hlogN2 hlarge
  intro A hA
  have hAcard :
      ((A.filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ) ≤
        (((range N).filter fun n =>
              ¬ ∃ d₁ d₂ : ℕ,
                  d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
          ℝ) := by
    norm_num
    exact Finset.card_le_card (Finset.filter_subset_filter _ hA)
  refine le_trans hAcard ?_
  have hz' : z ≤ c * log (N : ℝ) := by
    rw [div_le_iff₀ h0c] at hlogN2
    simpa [mul_comm] using hlogN2
  let X :=
    (range N).filter fun n =>
      ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p
  let Y :=
    fun m =>
      (range N).filter fun n =>
        m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p
  have hXbound : (X.card : ℝ) ≤ C * (log w / log z) * N := by
    exact hsieve N hlarge w z h2w h1z hz'
  have hYlocbound :
      ∀ m : ℕ,
        16 ≤ m →
          (m : ℝ) / 4 ≤ c * log ⌈(N : ℝ) / m⌉₊ →
            T ≤ ⌈(N : ℝ) / m⌉₊ →
              ((Y m).card : ℝ) ≤ C * (log y / log ((m : ℝ) / 4)) * (N / m + 1) := by
    intro m h16m hm hTm
    have h0m : 0 < m := by
      refine lt_of_lt_of_le ?_ h16m
      norm_num
    have h0m' : (0 : ℝ) < m := by exact_mod_cast h0m
    have h1m' : 1 < (m : ℝ) / 4 := by
      have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast h16m
      nlinarith
    have hcoeff_nonneg : 0 ≤ C * (log y / log ((m : ℝ) / 4)) := by
      refine mul_nonneg h0C.le ?_
      refine div_nonneg ?_ (Real.log_pos h1m').le
      exact Real.log_nonneg (le_trans one_le_two h2y)
    have hcard :
        (Y m).card ≤
          ((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card := by
      refine
        Finset.card_le_card_of_injOn
          (fun i => i / m)
          ?_
          ?_
      · intro n hn
        change n ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hn
        change
          n / m ∈
            (range ⌈(N : ℝ) / m⌉₊).filter
              (fun n => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p)
        rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
        refine ⟨?_, ?_⟩
        · rw [Nat.lt_ceil, Nat.cast_div hn.2.1 (by exact_mod_cast h0m.ne')]
          exact div_lt_div_of_pos_right (by exact_mod_cast hn.1) h0m'
        · intro p hp hpnm
          rcases hn.2.2 p hp (dvd_trans hpnm (Nat.div_dvd_of_dvd hn.2.1)) with hpy | hmp
          · exact Or.inl hpy
          · right
            rw [div_lt_iff₀ zero_lt_four]
            simpa [mul_comm] using hmp
      · intro a ha b hb hab
        change a ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at ha
        change b ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hb
        rw [Finset.mem_filter] at ha hb
        have ha' : a = (a / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m ha.2.1).1 rfl
        have hb' : b = (b / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m hb.2.1).1 rfl
        rw [ha', hb']
        exact congrArg (fun t => t * m) hab
    have hsieve' :
        (((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card :
          ℝ) ≤
          C * (log y / log ((m : ℝ) / 4)) * ⌈(N : ℝ) / m⌉₊ := by
      exact hsieve ⌈(N : ℝ) / m⌉₊ hTm y ((m : ℝ) / 4) h2y h1m' hm
    refine (Nat.cast_le.2 hcard).trans ?_
    have hceil : (⌈(N : ℝ) / m⌉₊ : ℝ) ≤ N / m + 1 := by
      exact le_of_lt (Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) / m by positivity))
    exact hsieve'.trans (mul_le_mul_of_nonneg_left hceil hcoeff_nonneg)
  let Y' := ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r).biUnion fun p => Y p
  have hcover :
      ((range N).filter fun n =>
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z) ⊆ X ∪ Y' := by
    intro n hn
    by_cases hXin : n ∈ X
    · exact Finset.mem_union.mpr (Or.inl hXin)
    · have hn_range : n ∈ range N := (Finset.mem_filter.mp hn).1
      have hn_forbid :
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z :=
        (Finset.mem_filter.mp hn).2
      have hnotX :
          ¬ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p := by
        intro hprop
        exact hXin (Finset.mem_filter.mpr ⟨hn_range, hprop⟩)
      rw [Finset.mem_union, Finset.mem_biUnion]
      right
      rw [not_forall] at hnotX
      rcases hnotX with ⟨p, hp⟩
      rw [Classical.not_imp, Classical.not_imp, not_or, not_lt, not_lt] at hp
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, hp.1⟩
        · exact Nat.ceil_le.mpr hp.2.2.1
        · exact (Nat.le_floor_iff' hp.1.ne_zero).mpr hp.2.2.2
      · rw [Finset.mem_filter]
        refine ⟨hn_range, hp.2.1, ?_⟩
        intro q hq hqn
        by_cases hqy : y ≤ q
        · right
          have hp4q : (p : ℝ) < 4 * q := by
            by_contra hp4q
            have h4qp : 4 * q ≤ p := by exact_mod_cast not_lt.mp hp4q
            exact hn_forbid ⟨q, p, hqn, hp.2.1, hqy, h4qp, hp.2.2.2⟩
          exact hp4q
        · left
          exact lt_of_not_ge hqy
  calc
    ((((range N).filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ)) ≤ ((X ∪ Y').card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
    _ ≤ (X.card : ℝ) + (Y'.card : ℝ) := by
      exact_mod_cast Finset.card_union_le X Y'
    _ ≤ C * (log w / log z) * N + (Y'.card : ℝ) := by
      rw [add_le_add_iff_right]
      exact hXbound
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => ((Y p).card : ℝ))) := by
      rw [add_le_add_iff_left]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => C * (log y / log (p / 4)) * (N / p + 1))) := by
      rw [add_le_add_iff_left]
      refine Finset.sum_le_sum ?_
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have h16p : 16 ≤ p := by
        have h16ceil : 16 ≤ ⌈w⌉₊ := by
          have h16ceilR : (16 : ℝ) ≤ ⌈w⌉₊ := le_trans h16w (Nat.le_ceil w)
          exact_mod_cast h16ceilR
        exact le_trans h16ceil hp.1.1
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos hp.2
      refine hYlocbound p h16p ?_ ?_
      · have hp_le_floor : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hp.1.2
        have hfloorlog_div : (4 : ℝ) * ⌊z⌋₊ / c ≤ log ((N : ℝ) / ⌊z⌋₊) := by
          rw [Real.log_div h0N.ne' h0zc.ne', le_sub_iff_add_le]
          exact hlogN1
        have hfloorlog : (4 : ℝ) * ⌊z⌋₊ ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          rw [div_le_iff₀ h0c] at hfloorlog_div
          simpa [mul_comm, mul_left_comm, mul_assoc] using hfloorlog_div
        have hfloor_le : (⌊z⌋₊ : ℝ) ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hfloor_nonneg : (0 : ℝ) ≤ ⌊z⌋₊ := by positivity
          nlinarith
        have hp4_le : (p : ℝ) / 4 ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hp4_le_floor : (p : ℝ) / 4 ≤ ⌊z⌋₊ := by
            nlinarith
          exact le_trans hp4_le_floor hfloor_le
        have hquot : (N : ℝ) / ⌊z⌋₊ ≤ (N : ℝ) / p := by
          exact div_le_div_of_nonneg_left h0N.le hp_pos hp_le_floor
        have hlogquot : log ((N : ℝ) / ⌊z⌋₊) ≤ log ((N : ℝ) / p) := by
          exact Real.log_le_log (div_pos h0N h0zc) hquot
        have hlogceil : log ((N : ℝ) / p) ≤ log ⌈(N : ℝ) / p⌉₊ := by
          refine Real.log_le_log (div_pos h0N hp_pos) ?_
          exact Nat.le_ceil _
        exact le_trans hp4_le (mul_le_mul_of_nonneg_left (le_trans hlogquot hlogceil) h0c.le)
      · rw [← Nat.cast_le (α := ℝ)]
        refine le_trans ?_ (Nat.le_ceil _)
        by_cases h0T : (0 : ℝ) < T
        · rw [le_div_iff₀ hp_pos]
          refine le_trans ?_ hTzN
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hp.1.2) h0T.le
        · exact (le_of_not_gt h0T).trans (by positivity)
    _ ≤ (N : ℝ) / (10 * D) + (N : ℝ) / (10 * D) := by
      refine add_le_add ?_ ?_
      · have htmp := mul_le_mul_of_nonneg_right hwzD h0N.le
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      · simp_rw [mul_assoc, mul_add]
        rw [Finset.sum_add_distrib]
        have hsum20 :
            Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * (N / p)) +
              Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * 1) ≤
              (N : ℝ) / (20 * D) + (N : ℝ) / (20 * D) := by
          refine add_le_add ?_ ?_
          · have hzsumC :
                C *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => log y / (log (p / 4) * p)) ≤
                  1 / (20 * D) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using (le_div_iff₀ h0C).mp hzsum
            have hEq :
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
              calc
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => (N : ℝ) * (C * (log y / (log (p / 4) * p)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      have hp0 : p ≠ 0 := (Nat.Prime.pos (Finset.mem_filter.mp hp).2).ne'
                      field_simp [hp0]
                _ = (N : ℝ) *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => C * (log y / (log (p / 4) * p))) := by
                      rw [Finset.mul_sum]
                _ = (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
                      rw [← Finset.mul_sum]
            rw [hEq]
            have htmp := mul_le_mul_of_nonneg_left hzsumC h0N.le
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
          · refine (le_div_iff₀ ?_).2 ?_
            · refine mul_pos ?_ hD
              norm_num
            · simpa [mul_assoc] using hweirdN
        have hsum10 : (N : ℝ) / (D * 20) + (N : ℝ) / (D * 20) = (N : ℝ) / (D * 10) := by
          field_simp [hD.ne']
          ring
        simpa [mul_assoc, mul_left_comm, mul_comm, hsum10] using hsum20
    _ = (N : ℝ) / (5 * D) := by
      field_simp [hD.ne']
      ring

lemma turan_primes_estimate :
    ∃ C : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - log (log (N : ℝ))) ^ 2) ≤
          C * (N : ℝ) * log (log (N : ℝ)) := by
  rcases sum_prime_counting with ⟨C1, hsum⟩
  rcases sum_prime_counting_sq with ⟨C2, hsumsq⟩
  let C : ℝ := C2 + 2 * C1
  refine ⟨C, ?_⟩
  filter_upwards
    [ hsum
    , hsumsq
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlargeSum hlargeSumSq hlargeN
  have hcardIcc : (Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  let L : ℝ := log (log (N : ℝ))
  let S1 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ)
  let S2 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ) ^ 2
  have hsum' : (N : ℝ) * L - C1 * N ≤ S1 := by
    simpa [L, S1, mul_assoc, mul_left_comm, mul_comm] using hlargeSum
  have hsumsq' : S2 ≤ (N : ℝ) * L ^ 2 + C2 * N * L := by
    simpa [L, S2, mul_assoc, mul_left_comm, mul_comm] using hlargeSumSq
  have hmul :
      (2 * L) * ((N : ℝ) * L - C1 * N) ≤ (2 * L) * S1 := by
    refine mul_le_mul_of_nonneg_left hsum' ?_
    positivity
  have hexpand :
      (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) =
        S2 - 2 * L * S1 + (N : ℝ) * L ^ 2 := by
    simp_rw [sub_sq, S1, S2]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcardIcc]
    ring
  rw [hexpand]
  dsimp [C]
  nlinarith

lemma filter_regular (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun n : ℕ =>
              n ≠ 0 ∧
                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
          ℝ) ≤
          (N : ℝ) / D := by
  rcases turan_primes_estimate with ⟨C, hturan⟩
  have h100 : (0 : ℝ) < 1 / 100 := by norm_num
  filter_upwards
    [ hturan
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (C / (1 / 100) / (1 / D * (1 / 100))))
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)) ] with
      N hNturan hlargeN hlargeN2 hlargeN3
  intro A hA
  by_contra h
  rw [not_le] at h
  let A' :=
    A.filter fun n : ℕ =>
      n ≠ 0 ∧
        ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
            (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  let L : ℝ := log (log (N : ℝ))
  let ε : ℝ := (1 / 100 : ℝ) * L
  have hcontr : C * (N : ℝ) * L < (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
    have hstep1 : C * (N : ℝ) * L ≤ ((N : ℝ) / D) * ε ^ 2 := by
      have htmp := hlargeN2
      dsimp [L] at htmp
      have hpos1 : 0 < (1 / D * (1 / 100 : ℝ)) := by positivity
      have hpos2 : 0 < (1 / 100 : ℝ) := by norm_num
      rw [div_le_iff₀ hpos1, div_le_iff₀ hpos2] at htmp
      have hNL_nonneg : 0 ≤ (N : ℝ) * L := mul_nonneg hlargeN3.le hlargeN.le
      calc
        C * (N : ℝ) * L = C * ((N : ℝ) * L) := by ring
        _ ≤ (L * (1 / D * (1 / 100 : ℝ)) * (1 / 100 : ℝ)) * ((N : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_right htmp hNL_nonneg
        _ = ((N : ℝ) / D) * ε ^ 2 := by
          dsimp [ε]
          ring
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos <| by
      dsimp [ε]
      refine mul_pos ?_ hlargeN
      norm_num
    have hstep2 : ((N : ℝ) / D) * ε ^ 2 < (A'.card : ℝ) * ε ^ 2 :=
      mul_lt_mul_of_pos_right h hεsq
    have hstep3 : (A'.card : ℝ) * ε ^ 2 ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      calc
        (A'.card : ℝ) * ε ^ 2 = A'.sum (fun _ => ε ^ 2) := by simp [nsmul_eq_mul]
        _ ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rw [Finset.mem_filter] at hn
          by_cases hlow : ((99 : ℝ) / 100) * L ≤ ω n
          · have hhigh : 2 * L < (ω n : ℝ) := by
              apply lt_of_not_ge
              intro hupper
              exact hn.2.2 ⟨by simpa using hlow, by simpa using hupper⟩
            have hεle : ε ≤ (ω n : ℝ) - L := by
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ (ω n : ℝ) - L := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ ((ω n : ℝ) - L) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            simpa using hsquare
          · have hεle : ε ≤ L - ω n := by
              have hlow' : (ω n : ℝ) < (99 : ℝ) / 100 * L := lt_of_not_ge hlow
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ L - ω n := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ (L - ω n) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            have hsame : (L - ω n) ^ 2 = ((ω n : ℝ) - L) ^ 2 := by ring
            exact hsame ▸ hsquare
    have hstep4 : A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) ≤
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
          intro hbad
          rw [hbad, Finset.mem_filter] at hm
          exact hm.2.1 rfl
        · have htempy := hA ((Finset.filter_subset _ _) hm)
          rw [Finset.mem_range] at htempy
          exact le_of_lt htempy
      · intro n _ _
        exact sq_nonneg _
    exact lt_of_lt_of_le (lt_of_le_of_lt hstep1 hstep2) (le_trans hstep3 hstep4)
  exact (not_lt_of_ge (by simpa [L] using hNturan)) hcontr

lemma log_helper (y : ℝ) (h : 0 < y) (h'' : y ≤ 1 / 2) : -2 * y ≤ log (1 - y) := by
  have hy1 : y < 1 := lt_of_le_of_lt h'' one_half_lt_one
  have hloginv : log ((1 - y)⁻¹) ≤ 2 * y := by
    refine le_trans (Real.log_le_sub_one_of_pos (inv_pos.2 (sub_pos.2 hy1))) ?_
    have hyinv_le : (1 - y)⁻¹ ≤ 2 := by
      have htwo : 2 ≤ 1 / y := by
        rw [le_div_iff₀ h]
        linarith
      simpa [one_div, inv_inv, h.ne'] using sub_one_div_inv_le_two (a := 1 / y) htwo
    have hy_nonneg : 0 ≤ y := h.le
    have hy1_ne : 1 - y ≠ 0 := sub_ne_zero.mpr (ne_of_lt hy1).symm
    calc
      (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by
        field_simp [hy1_ne]
        ring_nf
      _ ≤ y * 2 := mul_le_mul_of_nonneg_left hyinv_le hy_nonneg
      _ = 2 * y := by ring
  have hneglog : -log (1 - y) ≤ 2 * y := by
    simpa [Real.log_inv] using hloginv
  linarith

lemma nat_floor_real_le_floor {M : ℝ} {N : ℕ} (h : M ≤ N) :
    ⌊M⌋₊ ≤ ⌊(N : ℝ)⌋₊ := by
  simpa using (Nat.floor_le_of_le h)

lemma diff_mertens_sum_hlarge4 {N : ℕ}
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (hlarge5 : ‖log ((log ∘ Nat.cast) N)‖ ≤ (1 / 8 : ℝ) * ‖((log ∘ Nat.cast) N) ^ (1 : ℝ)‖) :
    log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
  have hmain : log (log (N : ℝ)) ≤ (1 / 8 : ℝ) * log (N : ℝ) := by
    simpa [Function.comp, Real.norm_eq_abs, abs_of_pos hloglogN, abs_of_nonneg hlogN.le,
      Real.rpow_one] using hlarge5
  nlinarith

lemma diff_mertens_sum_hsumM {N : ℕ} {b c M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (hlogN : 0 < log (N : ℝ))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹) :
    log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
        c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
      (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro hN
      subst hN
      norm_num at hlogN)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hfactor_pos : 0 < (1 : ℝ) - 8 / log (log (N : ℝ)) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  have hlogM :
      log M = (1 - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    rw [hM, Real.log_rpow h0N]
  have hloglogM :
      log (log M) = log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) := by
    rw [hlogM, Real.log_mul hfactor_pos.ne' hlogN.ne']
  have hlower := sub_le_of_abs_sub_le_left hlarge2'
  rw [hloglogM, hlogM] at hlower
  exact hlower

lemma diff_mertens_sum_hstep1 {N : ℕ} {M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h8loglogN : 8 < log (log (N : ℝ))) :
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) ≤
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  let A : Finset ℕ := (Finset.Icc 1 N).filter IsPrimePow
  let B : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow
  let S : Finset ℕ :=
    (range N).filter fun r : ℕ =>
      IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)
  have hN0 : N ≠ 0 := by
    intro hN
    subst hN
    norm_num at h8loglogN
  have h1leN : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hMleN : M ≤ (N : ℝ) := by
    rw [hM]
    calc
      (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ (N : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le h1leN ?_
        have hnonneg : 0 ≤ 8 / log (log (N : ℝ)) := by positivity
        linarith
      _ = (N : ℝ) := by simp
  have hfloorMleN : ⌊M⌋₊ ≤ N := by
    simpa [Nat.floor_natCast] using nat_floor_real_le_floor (M := M) (N := N) hMleN
  have hBsubA : B ⊆ A := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqpp⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqM⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans hqM hfloorMleN⟩, hqpp⟩
  have hSsub : S ⊆ A \ B := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqrange, hqprop⟩
    rcases hqprop with ⟨hqpp, hMq⟩
    have hqA : q ∈ A := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨
        Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt hqpp.pos, le_of_lt (Finset.mem_range.mp hqrange)⟩,
        hqpp
      ⟩
    have hqnotB : q ∉ B := by
      intro hqB
      rcases Finset.mem_filter.mp hqB with ⟨hqIcc, _hqpp⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hq1, hqM⟩
      have hfloorMltq : ⌊M⌋₊ < q := by
        exact (Nat.floor_lt' (Nat.ne_of_gt hqpp.pos)).2 (by simpa [hM] using hMq)
      exact not_lt_of_ge hqM hfloorMltq
    exact Finset.mem_sdiff.mpr ⟨hqA, hqnotB⟩
  have hsum_le : S.sum (fun q => (q : ℝ)⁻¹) ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub ?_
    intro q _hq _hnot
    have hq_nonneg : 0 ≤ (q : ℝ) := by
      exact_mod_cast Nat.zero_le q
    exact inv_nonneg.2 hq_nonneg
  calc
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) = S.sum (fun q => (q : ℝ)⁻¹) := by
          rfl
    _ ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := hsum_le
    _ = A.sum (fun q => (q : ℝ)⁻¹) - B.sum (fun q => (q : ℝ)⁻¹) := by
      exact Finset.sum_sdiff_eq_sub hBsubA
    _ = (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
      rfl

lemma diff_mertens_sum_hstep4 {N : ℕ} {b c C : ℝ}
    (hC : C = c / 2 + 16)
    (h0c : 0 < c)
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (h16loglogN : 16 ≤ log (log (N : ℝ)))
    (hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ)) :
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
      C / log (log (N : ℝ)) := by
  let L : ℝ := log (log (N : ℝ))
  let X : ℝ := log (N : ℝ)
  have hL : 0 < L := hloglogN
  have hX : 0 < X := hlogN
  have hy_pos : 0 < 8 / L := by
    positivity
  have hy_le : 8 / L ≤ (1 / 2 : ℝ) := by
    field_simp [hL.ne']
    nlinarith
  have hone_sub_pos : 0 < 1 - 8 / L := by
    rw [sub_pos]
    exact (div_lt_one hL).2 h8loglogN
  have hlog_term : -log (1 - 8 / L) ≤ 16 / L := by
    have htmp := log_helper (y := 8 / L) hy_pos hy_le
    have htmp' : -log (1 - 8 / L) ≤ 2 * (8 / L) := by
      linarith
    convert htmp' using 1
    ring_nf
  have hX_ge : 8 * L ≤ X := by
    nlinarith
  have hterm1 : c * X⁻¹ ≤ c / (8 * L) := by
    rw [div_eq_mul_inv]
    have h_inv : X⁻¹ ≤ (8 * L)⁻¹ := by
      have h8L_pos : 0 < 8 * L := by positivity
      simpa [one_div] using one_div_le_one_div_of_le h8L_pos hX_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hprod_ge : 4 * L ≤ (1 - 8 / L) * X := by
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 8 / L := by
      nlinarith
    have hhalfX : 4 * L ≤ (1 / 2 : ℝ) * X := by
      nlinarith
    have hhalfX_le : (1 / 2 : ℝ) * X ≤ (1 - 8 / L) * X := by
      exact mul_le_mul_of_nonneg_right hhalf_le hX.le
    exact le_trans hhalfX hhalfX_le
  have hterm2 : c * (((1 - 8 / L) * X)⁻¹) ≤ c / (4 * L) := by
    rw [div_eq_mul_inv]
    have hprod_pos : 0 < (1 - 8 / L) * X := mul_pos hone_sub_pos hX
    have h4L_pos : 0 < 4 * L := by positivity
    have h_inv : ((1 - 8 / L) * X)⁻¹ ≤ (4 * L)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le h4L_pos hprod_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hsum_c : c * X⁻¹ + c * (((1 - 8 / L) * X)⁻¹) ≤ c / (2 * L) := by
    have hsum' := add_le_add hterm1 hterm2
    refine hsum'.trans ?_
    field_simp [hL.ne']
    nlinarith
  have hleft :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
        c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := by
    simp [L, X, abs_of_pos hX, abs_of_pos (mul_pos hone_sub_pos hX)]
    ring
  have hright : c / (2 * L) + 16 / L = C / log (log (N : ℝ)) := by
    change c / (2 * L) + 16 / L = C / L
    rw [hC]
    field_simp [hL.ne']
  calc
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
      c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := hleft
    _ ≤ c / (2 * L) + 16 / L := by
      nlinarith [hsum_c, hlog_term]
    _ = C / log (log (N : ℝ)) := hright

lemma diff_mertens_sum :
    ∃ c : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        ((range N).filter fun (r : ℕ) =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (q : ℝ)⁻¹) ≤
          c / log (log (N : ℝ)) := by
  obtain ⟨b, hppr'⟩ := prime_power_reciprocal
  obtain ⟨c, h0c, hppr⟩ := hppr'.exists_pos
  let C : ℝ := c / 2 + 16
  refine ⟨C, ?_⟩
  have haux :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
      (show 0 < (1 : ℝ) / 8 by norm_num)
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually hppr.bound
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually hppr.bound
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (8 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (16 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N h0N hlarge1 hlarge2 hlogN hloglogN h8loglogN h16loglogN hlarge5
  let M : ℝ := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  have hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
    exact diff_mertens_sum_hlarge4 hlogN hloglogN hlarge5
  have hlarge1' :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹ := by
    simpa [Nat.floor_natCast, norm_inv, norm_eq_abs] using hlarge1
  have hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹ := by
    simpa [M, norm_inv, norm_eq_abs] using hlarge2
  have hsumN :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) := by
    have htmp := sub_le_of_abs_sub_le_right hlarge1'
    linarith
  have hsumM :
      log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hsumM (N := N) (b := b) (c := c) (M := M) rfl hlogN h8loglogN hlarge2'
  have hstep1 :
      ((range N).filter fun (r : ℕ) =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
          (fun q => (q : ℝ)⁻¹) ≤
        (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hstep1 (N := N) (M := M) rfl h8loglogN
  have hstep2 :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact sub_le_sub_right hsumN _
  have hstep3 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) := by
    exact sub_le_sub_left hsumM _
  have hstep4 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
        C / log (log (N : ℝ)) := by
    exact
      diff_mertens_sum_hstep4 (N := N) (b := b) (c := c) (C := C) rfl h0c hlogN hloglogN
        h8loglogN h16loglogN hlarge4
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

lemma filter_smooth (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun (n : ℕ) =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) ≤
          (N : ℝ) / D := by
  obtain ⟨c, hdiff⟩ := diff_mertens_sum
  filter_upwards [hdiff,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (D * 2)),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (0 : ℝ)),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (c / (1 / (2 * D)))),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_gt_atTop (0 : ℝ))] with
    N hdiff' hlarge1 hlarge2 hlarge3 hlarge4 hlarge5
  intro A hA
  let A' := A.erase 0
  have hlocal : ∀ q ∈ range N, 1 ≤ q → (A'.filter fun n => q ∣ n).card ≤ N / q := by
    intro q hq h1q
    calc
      (A'.filter fun n => q ∣ n).card ≤ ((Icc 1 N).filter fun n => q ∣ n).card := by
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        refine ⟨?_, hn.2⟩
        have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
        have hnN := hA hnA
        rw [Finset.mem_range] at hnN
        rw [Finset.mem_Icc]
        refine ⟨?_, le_of_lt hnN⟩
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1)
      _ = N / q := count_multiples h1q
  have hlocal' : ∀ q ∈ range N, 1 ≤ q → ((A'.filter fun n => q ∣ n).card : ℝ) ≤ (N : ℝ) / q := by
    intro q hq h1q
    exact le_trans (by exact_mod_cast hlocal q hq h1q) Nat.cast_div_le
  calc
    ((A.filter fun n =>
        ∃ q : ℕ,
          IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
        ℝ) ≤
        (((A'.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) + 1) := by
      exact_mod_cast (show
        (A.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card ≤
          (A'.filter fun n =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                  q ∣ n).card + 1 by
        rw [show A' = A.erase 0 by rfl, filter_erase]
        refine le_trans (Finset.card_le_card (Finset.insert_erase_subset 0 _)) ?_
        exact Finset.card_insert_le _ _)
    _ ≤
        (((range N).filter fun r : ℕ =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => ((A'.filter fun n => q ∣ n).card : ℝ))) + 1 := by
      rw [add_le_add_iff_right]
      have hdecomp :
          A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n) ⊆
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).biUnion
              (fun q => A'.filter fun n => q ∣ n) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_biUnion]
        rcases hn.2 with ⟨q, hqpp, hqlarge, hqdiv⟩
        refine ⟨q, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, hqpp, hqlarge⟩
          rw [Finset.mem_range]
          have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
          have hnN := hA hnA
          rw [Finset.mem_range] at hnN
          refine lt_of_le_of_lt ?_ hnN
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1) hqdiv
        · rw [Finset.mem_filter]
          exact ⟨hn.1, hqdiv⟩
      have hcard :
          (A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧
                    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                    q ∣ n)).card ≤
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (A'.filter fun n => q ∣ n).card)) := by
        refine (Finset.card_le_card hdecomp).trans ?_
        simpa using (Finset.card_biUnion_le (s := (range N).filter fun r : ℕ =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ))
          (t := fun q => A'.filter fun n => q ∣ n))
      exact_mod_cast hcard
    _ ≤
        (N : ℝ) *
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (1 : ℝ) / q)) +
          1 := by
      rw [add_le_add_iff_right, mul_sum]
      refine Finset.sum_le_sum ?_
      intro q hq
      rw [← div_eq_mul_one_div]
      rw [Finset.mem_filter] at hq
      exact hlocal' q hq.1 (le_of_lt (IsPrimePow.one_lt hq.2.1))
    _ ≤ (N : ℝ) / (2 * D) + 1 := by
      rw [add_le_add_iff_right, div_eq_mul_one_div (N : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc
        ((range N).filter fun r : ℕ =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (1 : ℝ) / q) =
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (q : ℝ)⁻¹) := by
          simp_rw [one_div]
        _ ≤ c / log (log (N : ℝ)) := hdiff'
        _ ≤ 1 / (2 * D) := by
          simp_rw [one_div]
          have htmp := (div_le_iff₀ (by
            rw [one_div_pos]
            exact mul_pos zero_lt_two hD)).mp hlarge4
          have htmp' : c ≤ (1 / (2 * D)) * log (log (N : ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
          simpa [Function.comp, one_div, mul_comm, mul_left_comm, mul_assoc] using
            (div_le_iff₀ hlarge5).2 htmp'
    _ ≤ (N : ℝ) / D := by
      have hhalf : 1 ≤ (N : ℝ) / (2 * D) := by
        rw [one_le_div (by positivity)]
        simpa [mul_comm] using hlarge2
      calc
        (N : ℝ) / (2 * D) + 1 ≤ (N : ℝ) / (2 * D) + (N : ℝ) / (2 * D) := by
          simpa [add_comm] using add_le_add_left hhalf ((N : ℝ) / (2 * D))
        _ = (N : ℝ) / D := by
          field_simp [hD.ne']
          ring

lemma nat_le_cast_real_sub {m n : ℕ} : (n : ℝ) - (m : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
  by_cases h : m < n
  · rw [Nat.cast_sub (le_of_lt h)]
  · have h' : n ≤ m := le_of_not_gt h
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast h')

lemma final_large_N (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            Filter.Eventually
              (fun N : ℕ =>
                (0 : ℝ) < N ∧
                  (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 < (N : ℝ) / (5 * D) ∧
                    (∀ A ⊆ range N,
                      ((A.filter fun (n : ℕ) =>
                            ∃ q : ℕ,
                              IsPrimePow q ∧
                                (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                                  q ∣ n).card :
                        ℝ) ≤
                        (N : ℝ) / (5 * D)) ∧
                      (∀ A ⊆ range N,
                        ((A.filter fun n : ℕ =>
                              n ≠ 0 ∧
                                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
                          ℝ) ≤
                          (N : ℝ) / (5 * D)) ∧
                        (∀ A ⊆ range N,
                          ((A.filter fun n =>
                                ¬ ∃ d₁ d₂ : ℕ,
                                    d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                      4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                            ℝ) ≤
                            (N : ℝ) / (5 * D)) ∧
                          z ≤ log (N : ℝ) ^ ((1 : ℝ) / 500) ∧
                            (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤
                              (N : ℝ) / (5 * D))
              atTop := by
  rcases filter_div D hD with ⟨y, z, h1y, hyz, h0z, hChelp, hChelp', hfilterdiv⟩
  refine ⟨y, z, h1y, hyz, h0z, ?_⟩
  have h5D : 0 < 5 * D := by
    refine mul_pos ?_ hD
    norm_num
  have h1pos : (0 : ℝ) < 1 := by norm_num
  filter_upwards
    [ eventually_gt_atTop 0
    , filter_smooth (5 * D) h5D
    , filter_regular (5 * D) h5D
    , hfilterdiv
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * (5 * D)))
    , ((tendsto_pow_rec_log_log_at_top h1pos).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (5 * D * 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (z ^ (500 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((1 / (1 / (5 * D) / 2)) ^ (200 : ℝ))) ] with
      N hlarge hsmooth hregular hdiv hlarge2 hlarge3 hlarge4 hlarge5 hlarge6
  dsimp at hlarge3 hlarge4 hlarge5 hlarge6
  refine ⟨by exact_mod_cast hlarge, ?_, hsmooth, hregular, hdiv, ?_, ?_⟩
  · calc
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 <
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 := by
            have hlt : 1 < ((N : ℝ) / (5 * D)) / 2 := by
              refine (_root_.lt_div_iff₀ zero_lt_two).2 ?_
              refine (_root_.lt_div_iff₀ h5D).2 ?_
              simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge2
            nlinarith
      _ ≤ (N : ℝ) / (5 * D) := by
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
        have hpow :
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) ≤ ((N : ℝ) / (5 * D)) / 2 := by
          have hfacpos : 0 < 5 * D * 2 := by positivity
          have hrecip :
              (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) ≤ 1 / (5 * D * 2) := by
            rw [Real.rpow_neg hNpos.le, ← one_div]
            exact one_div_le_one_div_of_le hfacpos hlarge3
          calc
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) =
                (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) * (N : ℝ) := by
                  rw [sub_eq_add_neg, add_comm, Real.rpow_add_one hNpos.ne']
            _ ≤ (1 / (5 * D * 2)) * (N : ℝ) := by
              exact mul_le_mul_of_nonneg_right hrecip (show 0 ≤ (N : ℝ) by exact hNpos.le)
            _ = ((N : ℝ) / (5 * D)) / 2 := by
              field_simp [hD.ne']
        calc
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 ≤
              ((N : ℝ) / (5 * D)) / 2 + ((N : ℝ) / (5 * D)) / 2 := by
                exact add_le_add hpow le_rfl
          _ = (N : ℝ) / (5 * D) := by ring
  · have h500 : (0 : ℝ) < 500 := by norm_num
    rw [← Real.rpow_le_rpow_iff _ _ h500, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
    · exact hlarge4
    · norm_num
    · exact le_of_lt hlarge5
    · exact le_of_lt h0z
    · exact Real.rpow_nonneg (le_of_lt hlarge5) _
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one h1y
    have hterm1 : 2 / y ≤ (1 / (5 * D)) / 2 := by
      have hterm1' : 2 / y ≤ 1 / (5 * D * 2) := by
        refine (_root_.div_le_iff₀ hypos).2 ?_
        have hc : 2 ≤ y * (1 / (5 * D * 2)) := by
          exact (_root_.div_le_iff₀ (show 0 < 1 / (5 * D * 2) by positivity)).1 hChelp'
        simpa [mul_comm] using hc
      calc
        2 / y ≤ 1 / (5 * D * 2) := hterm1'
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hterm2 : log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (1 / (5 * D)) / 2 := by
      rw [Real.rpow_neg hlarge5.le, ← one_div]
      have hroot :
          1 / (1 / (5 * D) / 2) ≤ log (N : ℝ) ^ ((1 : ℝ) / 200) := by
        have h200 : (0 : ℝ) < 200 := by norm_num
        rw [← Real.rpow_le_rpow_iff _ _ h200, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
        · exact hlarge6
        · norm_num
        · exact le_of_lt hlarge5
        · rw [one_div_nonneg]
          refine div_nonneg ?_ zero_le_two
          rw [one_div_nonneg]
          refine mul_nonneg ?_ hD.le
          norm_num
        · exact Real.rpow_nonneg hlarge5.le _
      have hrootpos : 0 < 1 / (1 / (5 * D) / 2) := by positivity
      calc
        1 / (log (N : ℝ) ^ ((1 : ℝ) / 200)) ≤ 1 / (1 / (1 / (5 * D) / 2)) :=
            one_div_le_one_div_of_le hrootpos hroot
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hsum : 2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ 1 / (5 * D) := by
      calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤
            (1 / (5 * D)) / 2 + (1 / (5 * D)) / 2 := by
              exact add_le_add hterm1 hterm2
        _ = 1 / (5 * D) := by rw [add_halves]
    calc
      (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤ (1 / (5 * D)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsum hNpos.le
      _ = (N : ℝ) / (5 * D) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]

theorem unit_fractions_upper_density' (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        0 ≤ z ∧
          ∀ A : Set ℕ,
            upper_density A > 1 / D →
              ∃ d ∈ Icc ⌈y⌉₊ ⌊z⌋₊,
                ∃ S : Finset ℕ,
                  (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 / d := by
  rcases final_large_N D hD with ⟨y, z, h1y, hyz, h0z, hfinal⟩
  refine ⟨y, z, h1y, le_of_lt h0z, ?_⟩
  intro A hA
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hfinal.and technical_prop)
  obtain ⟨N, hNN0, hAcard⟩ := frequently_atTop'.1 (frequently_nat_of hA) N0
  have hlargeN := (hN0 N (le_of_lt hNN0)).1
  have htech := (hN0 N (le_of_lt hNN0)).2
  dsimp at hlargeN
  have hzN := hlargeN.2.2.2.2.2.1
  have hyN := hlargeN.2.2.2.2.2.2
  let A' := (range N).filter fun n : ℕ => n ∈ A
  have hA'card : (N : ℝ) / D < A'.card := by
    have hNpos : 0 < (N : ℝ) := hlargeN.1
    have hAcard' : 1 / D < A'.card / N := by
      simpa [A'] using hAcard
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (lt_div_iff₀ hNpos).1 hAcard'
  let M := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  let A0 := A'.filter fun n : ℕ => (n : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))
  have hA0card : (A0.card : ℝ) < (N : ℝ) / (5 * D) := by
    calc
      (A0.card : ℝ) ≤ ((range ⌈(N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))⌉₊).card : ℝ) := by
        norm_cast
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_range, Nat.lt_ceil]
        exact hn.2
      _ < (N : ℝ) / (5 * D) := by
        rw [Finset.card_range]
        refine lt_trans (Nat.ceil_lt_add_one ?_) hlargeN.2.1
        exact Real.rpow_nonneg (le_of_lt hlargeN.1) _
  let A1 := A'.filter fun n ↦ ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  have hA1card : (A1.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A2 := A'.filter fun n ↦
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  have hA2card : (A2.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A3 := A'.filter fun n ↦
    ¬ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)
  have hA3card : (A3.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A'' := A' \ (A0 ∪ A1 ∪ A2 ∪ A3)
  have hUnionSub : A0 ∪ A1 ∪ A2 ∪ A3 ⊆ A' := by
    intro n hn
    rcases Finset.mem_union.mp hn with h012 | h3
    · rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · exact (Finset.mem_filter.mp h0).1
        · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · exact (Finset.mem_filter.mp h3).1
  have hA''card : (N : ℝ) / (5 * D) ≤ A''.card := by
    let x : ℝ := (N : ℝ) / (5 * D)
    have hA'card5 : 5 * x < A'.card := by
      dsimp [x]
      have hx : 5 * ((N : ℝ) / (5 * D)) = (N : ℝ) / D := by
        field_simp [hD.ne']
      rw [hx]
      exact hA'card
    have hsum4 : ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ 4 * x := by
      calc
        ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ (A0.card + A1.card + A2.card + A3.card : ℕ) := by
          norm_cast
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          exact Finset.card_union_le _ _
        _ ≤ 4 * x := by
          have hA0le : (A0.card : ℝ) ≤ x := le_of_lt hA0card
          dsimp [x] at hA0le hA1card hA2card hA3card ⊢
          push_cast
          nlinarith
    calc
      x ≤ (A'.card : ℝ) - (x + x + (x + x)) := by
        have hx4 : x + x + (x + x) = 4 * x := by ring
        rw [hx4]
        nlinarith
      _ ≤ (A'.card : ℝ) - (A0 ∪ A1 ∪ A2 ∪ A3).card := by
        dsimp [x] at hsum4 ⊢
        linarith
      _ ≤ A''.card := by
        dsimp [A'']
        rw [Finset.card_sdiff_of_subset hUnionSub]
        exact nat_le_cast_real_sub
  clear hA'card hA0card hA1card hA2card hA3card
  have hnotA0 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A0 := by
    intro n hn hn0
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl hn0
  have hnotA1 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A1 := by
    intro n hn hn1
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr hn1
  have hnotA2 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A2 := by
    intro n hn hn2
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hn2
  have hnotA3 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A3 := by
    intro n hn hn3
    exact (Finset.mem_sdiff.mp hn).2 <| Finset.mem_union.mpr <| Or.inr hn3
  have h0A'' : 0 ∉ A'' := by
    intro hz
    exact hnotA0 hz <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, by
      simpa using (Real.rpow_pos_of_pos hlargeN.1 (1 - (1 : ℝ) / log (log (N : ℝ))))⟩
  have hA''N : ∀ n ∈ A'', n < N := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1.1
  have hstep : ∃ S ⊆ A'', ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
    refine htech A'' ?_ y z h1y hyz hzN h0A'' ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range]
      exact lt_of_lt_of_le (hA''N n hn) (Nat.le_succ N)
    · intro n hn
      rw [← not_lt]
      intro hbad
      exact hnotA0 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (A''.card : ℝ) / N := by
          rw [le_div_iff₀ hlargeN.1]
          refine le_trans hyN hA''card
        _ ≤ rec_sum A'' := by
          rw [Finset.card_eq_sum_ones, rec_sum]
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnle : (n : ℝ) ≤ N := by
            exact_mod_cast Nat.le_of_lt (hA''N n hn)
          have hn0 : n ≠ 0 := by
            intro hzn
            exact h0A'' (hzn ▸ hn)
          have hnpos : 0 < (n : ℝ) := by
            exact Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
          exact one_div_le_one_div_of_le hnpos hnle
    · intro n hn
      by_contra hbad
      exact hnotA3 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · intro n hn
      rw [is_smooth]
      intro q hq hqn
      rw [← not_lt]
      intro hbad
      exact hnotA1 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, ⟨q, hq, hbad, hqn⟩⟩
    · rw [arith_regular]
      intro n hn
      by_contra hbad
      have hn0 : n ≠ 0 := by
        intro hz
        exact h0A'' (hz ▸ hn)
      exact hnotA2 hn <| Finset.mem_filter.mpr ⟨by
        rw [Finset.mem_sdiff] at hn
        exact hn.1, ⟨hn0, hbad⟩⟩
  clear htech
  rcases hstep with ⟨S, hS, d, hyd, hdz, hrecd⟩
  refine ⟨d, ?_, S, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact Nat.ceil_le.mpr hyd
    · exact (Nat.le_floor_iff (le_of_lt h0z)).mpr hdz
  · intro s hs
    have hs' := hS hs
    rw [Finset.mem_sdiff, Finset.mem_filter] at hs'
    exact hs'.1.2
  · rw [rec_sum] at hrecd
    exact hrecd

theorem unit_fractions_upper_density (A : Set ℕ) (hA : upper_density A > 0) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 := by
  classical
  let D := 2 / upper_density A
  have hD : 0 < D := div_pos zero_lt_two hA
  have hDA : 1 / D < upper_density A := by
    rw [show D = 2 / upper_density A by rfl, one_div_div]
    exact half_lt_self hA
  rcases unit_fractions_upper_density' D hD with ⟨y, z, h1y, h0z, hupp⟩
  let M := (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).sum fun d => d
  let good_set : Finset (Finset ℕ) → Prop := fun S =>
    (∀ s ∈ S, (s : Set ℕ) ⊆ A) ∧
      (S : Set (Finset ℕ)).PairwiseDisjoint id ∧
        ∀ s, ∃ d : ℕ, s ∈ S → y ≤ d ∧ (d : ℝ) ≤ z ∧ rec_sum s = 1 / d
  let P : ℕ → Prop := fun k => ∃ S : Finset (Finset ℕ), S.card = k ∧ good_set S
  let k : ℕ := Nat.findGreatest P (M + 1)
  have P0 : P 0 := by
    refine ⟨∅, ?_⟩
    simp [good_set]
  have Pk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk
  choose d' hd'₁ hd'₂ hd'₃ using hS₃
  let t : ℕ → ℕ := fun d => (S.filter fun s => d' s = d).card
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d
  · obtain ⟨d, d_pos, ht⟩ := h
    obtain ⟨T', hT', hd₂⟩ := Finset.exists_subset_card_eq (s := S.filter fun s => d' s = d) ht
    have hT'S : T' ⊆ S := hT'.trans (Finset.filter_subset _ _)
    refine ⟨T'.biUnion id, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_biUnion.mp hn with ⟨s, hsT, hns⟩
      exact hS₁ s (hT'S hsT) hns
    · change rec_sum (T'.biUnion id) = 1
      rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S)]
      have hsumT : T'.sum rec_sum = T'.sum (fun _ : Finset ℕ => (1 : ℚ) / d) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [(Finset.mem_filter.mp (hT' hi)).2] using (hd'₃ i (hT'S hi))
      rw [hsumT, Finset.sum_const, hd₂, nsmul_eq_mul]
      field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast d_pos.ne']
  · exfalso
    have hcount : ∀ d : ℕ, 0 < d → t d < d := by
      intro d hd
      by_contra hdt
      exact h ⟨d, hd, le_of_not_gt hdt⟩
    let A' : Set ℕ := A \ (S.biUnion id : Set ℕ)
    have hDA' : 1 / D < upper_density A' := by
      have hpres : upper_density A = upper_density A' := by
        dsimp [A']
        simpa using (upper_density_preserved (A := A) (S := S.biUnion id))
      rw [← hpres]
      exact hDA
    specialize hupp A' hDA'
    rcases hupp with ⟨d, hd, S', hS'₁, hS'₂⟩
    have hd' : y ≤ d ∧ (d : ℝ) ≤ z := by
      rw [Finset.mem_Icc] at hd
      refine ⟨?_, ?_⟩
      · exact le_trans (Nat.le_ceil y) (by exact_mod_cast hd.1)
      · exact le_trans (by exact_mod_cast hd.2) (Nat.floor_le h0z)
    have h1d : 1 ≤ d := by
      have : (1 : ℝ) ≤ d := le_trans h1y hd'.1
      exact_mod_cast this
    have hAS : Disjoint A' (S.biUnion id : Set ℕ) := by
      dsimp [A']
      simpa using (disjoint_sdiff_self_left : Disjoint (A \ (S.biUnion id : Set ℕ))
        (S.biUnion id : Set ℕ))
    have hS'A : (S' : Set ℕ) ⊆ A := by
      intro n hn
      exact (hS'₁ hn).1
    have hS'' : ∀ s ∈ S, Disjoint S' s := by
      intro s hs
      rw [← Finset.disjoint_coe]
      exact Disjoint.mono hS'₁ (Finset.subset_biUnion_of_mem id hs) hAS
    have hS''' : S' ∉ S := by
      intro hs
      exact (nonempty_of_rec_sum_recip h1d hS'₂).ne_empty (disjoint_self.mp (hS'' _ hs))
    have hPk1 : P (k + 1) := by
      refine ⟨insert S' S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hS''', hk]
      · refine ⟨?_, ?_, ?_⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hS'A
          · exact hS₁ s hs
        · simpa [Set.pairwiseDisjoint_insert_of_notMem hS''', hS₂] using fun s hs =>
            hS'' _ hs
        · intro s
          rcases eq_or_ne s S' with rfl | hs
          · exact ⟨d, fun _ => ⟨hd'.1, hd'.2, hS'₂⟩⟩
          · refine ⟨d' s, fun hs' => ?_⟩
            have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs' hs
            exact ⟨hd'₁ _ hsS, hd'₂ _ hsS, hd'₃ _ hsS⟩
    have hk_bound : k + 1 ≤ M + 1 := by
      rw [← hk, add_le_add_iff_right]
      have hSdecomp :
          (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).biUnion (fun d => S.filter fun s => d' s = d) = S := by
        refine Finset.biUnion_filter_eq_of_maps_to ?_
        intro n hn
        rw [Finset.mem_Icc]
        refine ⟨Nat.ceil_le.mpr (hd'₁ n hn), (Nat.le_floor_iff h0z).mpr (hd'₂ n hn)⟩
      rw [← hSdecomp]
      refine le_trans Finset.card_biUnion_le ?_
      refine Finset.sum_le_sum ?_
      intro d hd
      have hd' : d ∈ Finset.Icc ⌈y⌉₊ ⌊z⌋₊ := hd
      rw [Finset.mem_Icc, Nat.ceil_le] at hd'
      exact
        le_of_lt
          (hcount d (by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1y hd'.1))))
    have : k + 1 ≤ k := Nat.le_findGreatest hk_bound hPk1
    exact Nat.not_succ_le_self _ this

lemma rec_sum_union {A B : Finset ℕ} :
    (rec_sum (A ∪ B) : ℝ) ≤ rec_sum A + rec_sum B := by
  rw [← Rat.cast_add, Rat.cast_le, rec_sum, rec_sum, rec_sum, ← Finset.sum_union_inter,
    le_add_iff_nonneg_right, ← rec_sum]
  exact rec_sum_nonneg

lemma rec_sum_sdiff {A B : Finset ℕ} :
    (rec_sum A : ℝ) - rec_sum B ≤ rec_sum (A \ B) := by
  rw [← Rat.cast_sub, Rat.cast_le, tsub_le_iff_right,
    ← rec_sum_disjoint disjoint_sdiff_self_left]
  refine rec_sum_mono ?_
  rw [Finset.sdiff_union_self_eq_union]
  exact Finset.subset_union_left

lemma rec_sum_bUnion {I : Finset ℕ} (f : ℕ → Finset ℕ) :
    (rec_sum (I.biUnion f) : ℝ) ≤ I.sum (fun i => rec_sum (f i)) := by
  have hrat : rec_sum (I.biUnion f) ≤ I.sum (fun i => rec_sum (f i)) := by
    rw [rec_sum]
    exact sum_bUnion_le_sum_of_nonneg fun x hx => by
      exact div_nonneg zero_le_one (show 0 ≤ (x : ℚ) by exact_mod_cast Nat.zero_le x)
  exact_mod_cast hrat

lemma this_particular_tends_to :
    Tendsto (fun x : ℝ => x ^ (log (log (log x)) / log (log x))) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_pow_rec_log_log_at_top zero_lt_one)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop 0,
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)).eventually_ge_atTop 1]
      with x hx hx' hx''
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  have hmul := mul_le_mul_of_nonneg_right hx'' (one_div_nonneg.mpr hx')
  simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma Ioc_subset_Ioc_union_Ioc {a b c : ℕ} :
    Ioc a c ⊆ Ioc a b ∪ Ioc b c := by
  rw [← Finset.coe_subset, Finset.coe_union, Finset.coe_Ioc, Finset.coe_Ioc, Finset.coe_Ioc]
  exact Set.Ioc_subset_Ioc_union_Ioc

lemma bUnion_range_Ioc (N : ℕ) (f : ℕ → ℕ) :
    Ioc (f N) (f 0) ⊆ (range N).biUnion (fun i : ℕ => Ioc (f (i + 1)) (f i)) := by
  induction N with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert]
      have hsubset :
          Ioc (f (n + 1)) (f 0) ⊆ Ioc (f (n + 1)) (f n) ∪ Ioc (f n) (f 0) := by
        exact Ioc_subset_Ioc_union_Ioc
      exact subset_trans hsubset (Finset.union_subset_union Subset.rfl ih)

lemma this_fun_increasing_aux : StrictMonoOn (fun x : ℝ => exp x / x ^ 2) (Set.Ici 2) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 2) ?_ ?_
  · refine Real.continuous_exp.continuousOn.div (continuous_id.pow 2).continuousOn ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_two hx
    exact pow_ne_zero 2 hx0.ne'
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := lt_trans zero_lt_two hx
    change 0 < deriv (exp / fun x : ℝ => x ^ 2) x
    rw [deriv_div differentiableAt_exp (differentiableAt_pow 2) (pow_ne_zero 2 hx0.ne')]
    have hexp : deriv exp x = exp x := by
      exact congrFun Real.deriv_exp x
    have hpow : deriv (fun x : ℝ => x ^ 2) x = 2 * x := by
      calc
        deriv (fun x : ℝ => x ^ 2) x = (2 : ℝ) * x ^ (2 - 1) := by
          exact deriv_pow_field (𝕜 := ℝ) (x := x) 2
        _ = 2 * x := by simp
    rw [hexp, hpow, sq, ← mul_sub, ← sub_mul]
    exact div_pos (mul_pos (exp_pos _) (mul_pos (sub_pos_of_lt hx) hx0))
      (pow_pos (mul_pos hx0 hx0) 2)

lemma this_fun_increasing' :
    ∀ᶠ N in (atTop : Filter ℝ),
      ∀ M, N ≤ M → log N / log (log N) ^ 2 ≤ log M / log (log M) ^ 2 := by
  filter_upwards
      [ (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop 2
      , tendsto_log_atTop.eventually_gt_atTop 0
      , eventually_gt_atTop (0 : ℝ) ] with N hN hNl0 hN0 M hNM
  have hl : log N ≤ log M := log_le_log_of_le hN0 hNM
  have hll : log (log N) ≤ log (log M) := log_le_log_of_le hNl0 hl
  simpa [Function.comp, Real.exp_log hNl0, Real.exp_log (hNl0.trans_le hl)] using
    this_fun_increasing_aux.monotoneOn hN (le_trans hN hll) hll

lemma this_fun_increasing :
    ∃ C : ℝ,
      ∀ N M : ℕ,
        C ≤ N ∧ N ≤ M →
          log (N : ℝ) / (log (log (N : ℝ))) ^ 2 ≤
            log (M : ℝ) / (log (log (M : ℝ))) ^ 2 := by
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp this_fun_increasing'
  refine ⟨C, ?_⟩
  intro N M h
  exact hC N h.1 M (by exact_mod_cast h.2)

lemma harmonic_sum_bound_two' :
    ∀ᶠ N in (atTop : Filter ℝ),
      (range ⌈N⌉₊).sum (fun n => (1 : ℝ) / n) ≤ 2 * log N := by
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp harmonic_sum_bound_two
  filter_upwards [eventually_ge_atTop ((C : ℝ) + 1), eventually_gt_atTop (1 : ℝ)] with N hN h1N
  have hN' : (C : ℝ) ≤ N - 1 := by
    linarith
  have hCceil : C ≤ ⌈N - 1⌉₊ := by
    have haux : (C : ℝ) ≤ (⌈N - 1⌉₊ : ℝ) := le_trans hN' (Nat.le_ceil _)
    exact_mod_cast haux
  specialize hC ⌈N - 1⌉₊ hCceil
  calc
    (range ⌈N⌉₊).sum (fun n => (1 : ℝ) / n)
        ≤ (range (⌈N - 1⌉₊ + 1)).sum (fun n => (1 : ℝ) / n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            rw [Finset.mem_range] at hn ⊢
            exact lt_of_lt_of_le hn <| by
              refine Nat.ceil_le.mpr ?_
              calc
                N = (N - 1) + 1 := by ring
                _ ≤ (⌈N - 1⌉₊ : ℝ) + 1 := by
                  gcongr
                  exact Nat.le_ceil (N - 1)
                _ = ↑(⌈N - 1⌉₊ + 1) := by norm_num
          · intro n _ _
            exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    _ ≤ 2 * log (⌈N - 1⌉₊ : ℝ) := hC
    _ ≤ 2 * log N := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          refine log_le_log_of_le ?_ ?_
          · exact_mod_cast Nat.ceil_pos.mpr (sub_pos.mpr h1N)
          · have hceil_lt : (⌈N - 1⌉₊ : ℝ) < N := by
              linarith [Nat.ceil_lt_add_one (show 0 ≤ N - 1 by linarith)]
            exact hceil_lt.le

lemma harmonic_sum_bound' :
    ∃ C : ℝ,
      0 < C ∧
        ∀ N : ℝ,
          1 ≤ N → (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n) ≤ C * log (2 * N) := by
  obtain ⟨C₁, hharmonic⟩ := Filter.eventually_atTop.mp harmonic_sum_bound_two
  let C₁' : ℕ := max C₁ 2
  let I : Finset ℕ := Ico 1 C₁'
  let f : ℕ → ℝ := fun M => (Icc 1 M).sum (fun n => (1 : ℝ) / n)
  have hIne : I.Nonempty := by
    simpa [I] using
      (Finset.nonempty_Ico.mpr (lt_of_lt_of_le one_lt_two (le_max_right C₁ 2)) :
        (Ico 1 C₁').Nonempty)
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image I f hIne
  let C : ℝ := max 2 (f y / log 2)
  have h0C : 0 < C := lt_of_lt_of_le zero_lt_two (le_max_left _ _)
  refine ⟨C, h0C, ?_⟩
  intro N h1N
  have h0N : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have h1f : 1 ≤ ⌊N⌋₊ := by
    refine Nat.le_floor ?_
    exact_mod_cast h1N
  by_cases hcases : ⌊N⌋₊ < C₁
  · have hmem : ⌊N⌋₊ ∈ I := by
      simpa [I] using
        (show ⌊N⌋₊ ∈ Ico 1 C₁' from by
          rw [Finset.mem_Ico]
          exact ⟨h1f, lt_of_lt_of_le hcases (le_max_left C₁ 2)⟩)
    calc
      (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n)
          = f ⌊N⌋₊ := rfl
      _ ≤ f y := hmax _ hmem
      _ = (f y / log 2) * log 2 := by
            rw [div_mul_cancel₀ _]
            exact Real.log_ne_zero_of_pos_of_ne_one zero_lt_two (by norm_num)
      _ ≤ C * log 2 := by
            refine mul_le_mul_of_nonneg_right (le_max_right 2 (f y / log 2)) ?_
            exact (Real.log_pos one_lt_two).le
      _ ≤ C * (log 2 + log N) := by
            have hlogN : 0 ≤ log N := Real.log_nonneg h1N
            nlinarith [le_of_lt h0C, hlogN]
      _ = C * log (2 * N) := by
            rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) h0N.ne', mul_add]
  · have hcases' : C₁ ≤ ⌊N⌋₊ := Nat.le_of_not_gt hcases
    specialize hharmonic ⌊N⌋₊ hcases'
    calc
      (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n)
          ≤ (range (⌊N⌋₊ + 1)).sum (fun n => (1 : ℝ) / n) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro n hn
              rw [Finset.mem_Icc] at hn
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le hn.2
            · intro n _ _
              exact one_div_nonneg.mpr (Nat.cast_nonneg n)
      _ ≤ 2 * log ⌊N⌋₊ := by
            simpa using hharmonic
      _ ≤ C * log N := by
            have h2C : (2 : ℝ) ≤ C := le_max_left _ _
            have hfloor_le : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le h0N.le
            have hfloor_pos : 0 < (⌊N⌋₊ : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le zero_lt_one h1f)
            have hlogfloor_le : log ⌊N⌋₊ ≤ log N := log_le_log_of_le hfloor_pos hfloor_le
            have hlogfloor_nonneg : 0 ≤ log ⌊N⌋₊ := by
              exact Real.log_nonneg (by exact_mod_cast h1f)
            exact mul_le_mul h2C hlogfloor_le hlogfloor_nonneg (le_of_lt h0C)
      _ ≤ C * log (2 * N) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h0C)
            exact log_le_log_of_le h0N (by nlinarith)

lemma another_this_particular_tends_to :
    Tendsto (fun x : ℝ => log x / log (log x)) atTop atTop := by
  have h : Tendsto (fun x : ℝ => x / log x) atTop atTop := by
    simpa using tendsto_mul_add_div_pow_log_at_top (1 : ℝ) 0 1 zero_lt_one
  simpa using h.comp tendsto_log_atTop

lemma this_function_big_tends_to :
    Tendsto (fun x : ℝ => x ^ (log (log (log x)) / log (log x))) atTop atTop := by
  simpa using this_particular_tends_to

lemma now_last_large_N :
    Filter.Eventually
      (fun N : ℕ =>
        (198 : ℝ) / 199 * log (log (N : ℝ)) ≤
          log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ)))
      atTop := by
  filter_upwards
      [ ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (199 : ℝ))
      , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (0 : ℝ))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (0 : ℝ)) ] with
    N hlarge h0log h0log2 h0log3 h0log4
  have h0log2' : 0 < log (log (N : ℝ)) := by
    simpa using h0log2
  have hlarge' : (199 : ℝ) * log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) := by
    exact (_root_.le_div_iff₀ h0log3).mp hlarge
  have hsmall :
      log (log (log (N : ℝ))) ≤ (1 / 199 : ℝ) * log (log (N : ℝ)) := by
    nlinarith
  have hsub :
      log (log (log (N : ℝ))) - log (log (log (log (N : ℝ)))) ≤
        (1 / 199 : ℝ) * log (log (N : ℝ)) := by
    exact (sub_le_self _ (le_of_lt h0log4)).trans hsmall
  have hrewrite :
      log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ)) =
        log (log (N : ℝ)) -
          (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
    have hmul :
        log ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) =
          log (log (log (log (N : ℝ))) / log (log (N : ℝ))) + log (log (N : ℝ)) := by
      have hquot_ne : log (log (log (N : ℝ))) / log (log (N : ℝ)) ≠ 0 := by
        exact div_ne_zero (ne_of_gt h0log3) (ne_of_gt h0log2')
      simpa using Real.log_mul hquot_ne (ne_of_gt h0log)
    have hdiv :
        log (log (log (log (N : ℝ))) / log (log (N : ℝ))) =
          log (log (log (log (N : ℝ)))) - log (log (log (N : ℝ))) := by
      simpa using Real.log_div (ne_of_gt h0log3) (ne_of_gt h0log2')
    calc
      log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ))
          = log (log (log (log (N : ℝ))) / log (log (N : ℝ))) + log (log (N : ℝ)) := by
              simpa using hmul
      _ = (log (log (log (log (N : ℝ)))) - log (log (log (N : ℝ)))) + log (log (N : ℝ)) := by
            rw [hdiv]
      _ = log (log (N : ℝ)) -
            (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
            ring
  have hfinal :
      (198 : ℝ) / 199 * log (log (N : ℝ)) ≤
        log (log (N : ℝ)) -
          (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
    nlinarith
  rw [hrewrite]
  exact hfinal

lemma large_helper (c C : ℝ) (hc1 : c < 1) (h0C : 0 < C) :
    ∀ᶠ N in (atTop : Filter ℝ),
      log N ^ c < (log (log (log N)) / log (log N) * log N) * C := by
  have hc : 0 < -c + 1 := by
    rw [add_comm, ← sub_eq_add_neg]
    exact sub_pos.mpr hc1
  filter_upwards
      [ tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (log C⁻¹ / ((-c + 1) / 2)))
      , (another_this_particular_tends_to.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (1 / ((-c + 1) / 2)))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (0 : ℝ))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (1 : ℝ)) ] with
    N hN hN₁ hN₂ hN₃ hN₄ hN₅
  rw [← _root_.div_lt_iff₀ h0C, div_eq_mul_one_div, ← _root_.lt_div_iff₀' (show 0 < log N ^ c by
      exact Real.rpow_pos_of_pos hN _), div_eq_mul_one_div _ (log N ^ c), one_div, one_div,
    ← Real.rpow_neg hN.le c, mul_assoc, mul_comm (log N), ← Real.rpow_add_one hN.ne' (-c),
    div_eq_mul_one_div]
  transitivity (1 / log (log N)) * log N ^ (-c + 1)
  · rw [mul_comm, ← div_eq_mul_one_div]
    refine (_root_.lt_div_iff₀ hN₁).2 ?_
    refine (Real.log_lt_log_iff ?_ ?_).mp ?_
    · refine mul_pos ?_ hN₁
      rw [inv_pos]
      exact h0C
    · exact Real.rpow_pos_of_pos hN _
    rw [Real.log_rpow hN, Real.log_mul (inv_ne_zero h0C.ne') (ne_of_gt hN₁),
      ← add_halves (-c + 1), add_mul]
    refine add_lt_add ?_ ?_
    · exact (_root_.div_lt_iff₀' (show 0 < (-c + 1) / 2 by
          exact div_pos hc zero_lt_two)).mp hN₂
    · have haux : 1 < (((-c + 1) / 2) * log (log N)) / log (log (log N)) := by
        have : 1 < ((-c + 1) / 2) * (log (log N) / log (log (log N))) := by
          exact (_root_.div_lt_iff₀' (show 0 < (-c + 1) / 2 by
            exact div_pos hc zero_lt_two)).mp hN₃
        simpa [mul_div_assoc] using this
      exact (_root_.one_lt_div hN₄).mp haux
  · rw [mul_assoc]
    refine lt_mul_of_one_lt_left ?_ hN₅
    refine mul_pos ?_ ?_
    · rw [one_div_pos]
      exact hN₁
    · exact Real.rpow_pos_of_pos hN _

lemma the_last_large_N : ∀ C : ℝ, 0 < C →
    Filter.Eventually
      (fun N : ℕ =>
        log (N : ℝ) ^ ((3 : ℝ) / 4) ≤
            log (N : ℝ) * (log (log (log (N : ℝ))) / log (log (N : ℝ))) ∧
          ((⌈log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                (2 * log (log (N : ℝ)))⌉₊ : ℝ) *
              (2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
                C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) <
            (2 + 2 * C) * (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)))
      atTop := by
  intro C h0C
  have htemp' : ((3 : ℝ) / 4) < 1 := by norm_num
  have htemp₂ : ((251 : ℝ) / 500) < 1 := by norm_num
  have htemp₃ : ((1 : ℝ) / 500) < 1 := by norm_num
  have htemp₄ : (0 : ℝ) < 1 / 4 := by norm_num
  filter_upwards
      [ tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((3 : ℝ) / 4) (1 : ℝ) htemp' zero_lt_one)
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((1 : ℝ) / 500) ((1 : ℝ) / 4) htemp₃ htemp₄)
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((251 : ℝ) / 500) ((1 : ℝ) / 2) htemp₂ one_half_pos)
      , ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (2 * (C * 1)))
      , tendsto_log_log_coe_at_top (eventually_ge_atTop (log 2 / (1 / 4 / 2)))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (1 : ℝ))
      , (another_this_particular_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop (1 : ℝ))
      , ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (8 : ℝ)) ] with
    N h1logN hlarge1 hlarge2 hlarge3 hweird h0loglogN hloglogN' hloglogN'' h1log3 hbig hbig₂
  have h0log3 : 0 < log (log (log (N : ℝ))) := lt_trans zero_lt_one h1log3
  have h0logN : 0 < log (N : ℝ) := lt_trans zero_lt_one h1logN
  have h0loglogNr : 0 < log (log (N : ℝ)) := by
    simpa using h0loglogN
  have hloglogN'_ineq : 2 * C < log (log (N : ℝ)) := by
    simpa using hloglogN'
  have hlarge₃ : 2 * log (log (N : ℝ)) ≤ log (N : ℝ) ^ ((1 : ℝ) / 4) := by
    refine
      (Real.log_le_log_iff (mul_pos zero_lt_two h0loglogNr) (Real.rpow_pos_of_pos h0logN _)).mp
        ?_
    rw [Real.log_rpow h0logN, Real.log_mul two_ne_zero h0loglogNr.ne', ← add_halves ((1 : ℝ) / 4),
      add_mul]
    have hpart1 : log 2 ≤ log (log (N : ℝ)) * ((1 : ℝ) / 8) := by
      have htmp : (8 : ℝ) * log 2 ≤ log (log (N : ℝ)) := by
        have hloglogN''_ineq : log 2 / ((1 / 4 : ℝ) / 2) ≤ log (log (N : ℝ)) := by
          simpa using hloglogN''
        nlinarith [hloglogN''_ineq]
      nlinarith
    have hpart2 : log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) * ((1 : ℝ) / 8) := by
      have htmp : (8 : ℝ) * log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) := by
        exact (_root_.le_div_iff₀ h0log3).mp hbig₂
      nlinarith
    nlinarith
  refine ⟨?_, ?_⟩
  · simpa [mul_comm, mul_left_comm, mul_assoc] using le_of_lt hlarge1
  · transitivity
      (log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) + 1) *
        (2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
          C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ))
    · refine mul_lt_mul_of_pos_right ?_ ?_
      · exact Nat.ceil_lt_add_one <| by
          refine mul_nonneg ?_ ?_
          · refine Real.log_nonneg ?_
            exact hweird
          · exact mul_nonneg zero_le_two (le_of_lt h0loglogNr)
      · refine add_pos ?_ ?_
        · exact mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN _)
        · refine mul_pos ?_ h0logN
          refine mul_pos h0C ?_
          rw [one_div_pos]
          exact sq_pos_of_pos h0loglogN
    · rw [add_mul, mul_add, add_rotate, add_rotate, add_mul, add_mul]
      refine add_lt_add_of_lt_of_le ?_ ?_
      · have hsum5 :
            2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
                C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
          rw [← add_halves ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ))]
          refine add_lt_add ?_ ?_
          · rw [_root_.lt_div_iff₀ zero_lt_two, mul_comm, ← mul_assoc]
            norm_num
            rw [← _root_.lt_div_iff₀' zero_lt_four, div_eq_mul_one_div _ (4 : ℝ)]
            exact hlarge2
          · refine (_root_.lt_div_iff₀' zero_lt_two).2 ?_
            have hmain :
                2 * C < log (log (log (N : ℝ))) * log (log (N : ℝ)) := by
              exact lt_trans hloglogN'_ineq (lt_mul_of_one_lt_left h0loglogNr h1log3)
            have hscaled := mul_lt_mul_of_pos_right hmain (div_pos h0logN (sq_pos_of_pos h0loglogN))
            convert hscaled using 1
            all_goals
              field_simp [h0loglogNr.ne']
        have hsum6 :
            log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                (2 * log (log (N : ℝ)) *
                  (log (N : ℝ) ^ ((1 : ℝ) / 500) + log (N : ℝ) ^ ((1 : ℝ) / 500))) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
          transitivity
              log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                (2 * log (N : ℝ) ^ ((1 : ℝ) / 500))
          · have hfac :
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) <
                  log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) := by
              refine mul_lt_mul ?_ ?_ ?_ ?_
              · transitivity log (log (log (N : ℝ)))
                · refine Real.log_lt_log ?_ ?_
                  · exact div_pos h0loglogNr h0log3
                  · exact div_lt_self h0loglogNr h1log3
                · have hmid : log (log (log (N : ℝ))) < 2 * log (log (N : ℝ)) := by
                    transitivity log (log (N : ℝ))
                    · refine Real.log_lt_log h0loglogNr ?_
                      rw [← _root_.one_lt_div]
                      · exact hbig
                      · exact h0loglogNr
                    · exact lt_mul_of_one_lt_left h0loglogNr one_lt_two
                  exact lt_of_lt_of_le hmid hlarge₃
              · exact hlarge₃
              · exact mul_pos zero_lt_two h0loglogNr
              · exact Real.rpow_nonneg (le_of_lt h0logN) ((1 : ℝ) / 4)
            have hmul :
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) *
                    (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) <
                  (log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4)) *
                    (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) :=
              mul_lt_mul_of_pos_right hfac
                (mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN ((1 : ℝ) / 500)))
            simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
          · have hlarge3' :
                2 * log (N : ℝ) ^ ((251 : ℝ) / 500) <
                  (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
              nlinarith [hlarge3]
            calc
              log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                  (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) =
                2 * log (N : ℝ) ^ ((251 : ℝ) / 500) := by
                  calc
                    log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                        (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) =
                      2 *
                        (log (N : ℝ) ^ (((1 : ℝ) / 4) + (1 / 4)) *
                          log (N : ℝ) ^ ((1 : ℝ) / 500)) := by
                        rw [← Real.rpow_add h0logN]
                        ring
                    _ = 2 * log (N : ℝ) ^ ((((1 : ℝ) / 4) + (1 / 4)) + (1 / 500)) := by
                        rw [← Real.rpow_add h0logN]
                    _ = 2 * log (N : ℝ) ^ ((251 : ℝ) / 500) := by norm_num
              _ < (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := hlarge3'
        have hsum :
            2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) + C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) +
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                  (2 * log (log (N : ℝ)) *
                    (log (N : ℝ) ^ ((1 : ℝ) / 500) + log (N : ℝ) ^ ((1 : ℝ) / 500))) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) +
                (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
              exact add_lt_add hsum5 hsum6
        convert hsum using 1
        all_goals
          ring_nf
      · have hy_nonneg :
            0 ≤ C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) := by
          positivity
        have hlog_le :
            log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) ≤ log (log (log (N : ℝ))) := by
          refine Real.log_le_log ?_ ?_
          · exact div_pos h0loglogN h0log3
          · exact div_le_self (le_of_lt h0loglogN) (le_of_lt h1log3)
        calc
          log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
              (2 * log (log (N : ℝ))) * (C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) ≤
            log (log (log (N : ℝ))) *
              (2 * log (log (N : ℝ))) * (C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) := by
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hlog_le
                  (mul_nonneg (mul_nonneg zero_le_two (le_of_lt h0loglogNr)) hy_nonneg)
          _ = 2 * C * (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
            field_simp [h0loglogNr.ne']

lemma how_large_can_we_go (C : ℝ) (h0C : 0 < C) :
    ∀ᶠ N in (atTop : Filter ℝ),
      log N ^ ((1 : ℝ) / 1000) ≤ (log (log (log N)) / log (log N) * log N) * C := by
  have hsmall : ((1 : ℝ) / 1000) < 1 := by norm_num
  filter_upwards [large_helper ((1 : ℝ) / 1000) C hsmall h0C] with N hN
  exact le_of_lt hN

lemma crude_ps (p : ℕ → Prop) [DecidablePred p] (δ : ℝ) (Y : ℝ) (h0δ : 0 < δ)
    (h1Y : 1 ≤ Y) (N : ℕ)
    (h : ∀ X : ℝ, Y ≤ X ∧ X ≤ N →
      (((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p).card : ℝ) ≤ δ * X)
    (h2N : 2 ≤ N) :
    ((Icc ⌈Y⌉₊ N).filter p).sum (fun n => (1 : ℝ) / n) ≤
      (2 / log 2) * δ * log (N : ℝ) := by
  have h0Y : 0 < Y := lt_of_lt_of_le zero_lt_one h1Y
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_two h2N
  by_cases hYN : Y ≤ N
  · let f : ℕ → Finset ℕ := fun i =>
      (Ico ⌈2 ^ (i : ℝ) * Y⌉₊ ⌈2 * (2 ^ (i : ℝ) * Y)⌉₊).filter p
    let I : Finset ℕ := range (⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ + 1)
    have hcont : ((Icc ⌈Y⌉₊ N).filter p) ⊆ I.biUnion f := by
      intro n hn
      rw [Finset.mem_biUnion]
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : 0 < (n : ℝ) := by
        have hceilY : 0 < (⌈Y⌉₊ : ℝ) := by
          exact_mod_cast Nat.ceil_pos.mpr h0Y
        exact hceilY.trans_le (by exact_mod_cast hn.1.1)
      have haux : 0 < (n : ℝ) / Y := div_pos hn0 h0Y
      have haux' : 0 ≤ Real.logb 2 ((n : ℝ) / Y) := by
        refine Real.logb_nonneg one_lt_two ?_
        rw [one_le_div h0Y]
        exact le_trans (Nat.le_ceil Y) (by exact_mod_cast hn.1.1)
      let i : ℕ := ⌊Real.logb 2 ((n : ℝ) / Y)⌋₊
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        refine Nat.le_floor ?_
        refine le_trans (Nat.floor_le haux') ?_
        exact (Real.logb_le_logb one_lt_two haux (div_pos h0N h0Y)).2 <|
          div_le_div_of_nonneg_right (by exact_mod_cast hn.1.2) h0Y.le
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Ico]
          refine ⟨?_, ?_⟩
          · rw [Nat.ceil_le]
            have hi_le : (i : ℝ) ≤ Real.logb 2 ((n : ℝ) / Y) := Nat.floor_le haux'
            have hpow_le : (2 : ℝ) ^ (i : ℝ) ≤ (n : ℝ) / Y :=
              (Real.le_logb_iff_rpow_le one_lt_two haux).1 hi_le
            exact (_root_.le_div_iff₀ h0Y).mp hpow_le
          · refine Nat.lt_ceil.mpr ?_
            have hlogb_lt : Real.logb 2 ((n : ℝ) / Y) < ((i + 1 : ℕ) : ℝ) := by
              simpa [i] using Nat.lt_floor_add_one (Real.logb 2 ((n : ℝ) / Y))
            have hpow_lt : (n : ℝ) / Y < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) :=
              (Real.logb_lt_iff_lt_rpow one_lt_two haux).1 hlogb_lt
            have hupper' : (n : ℝ) < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y :=
              (_root_.div_lt_iff₀ h0Y).mp hpow_lt
            have heq : (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y = 2 * ((2 : ℝ) ^ (i : ℝ) * Y) := by
              rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ']
              ring
            calc
              (n : ℝ) < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y := hupper'
              _ = 2 * ((2 : ℝ) ^ (i : ℝ) * Y) := heq
        · exact hn.2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcont ?_) ?_
    · intro n _ _
      exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    refine le_trans (sum_bUnion_le_sum_of_nonneg ?_) ?_
    · intro n hn
      exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    have hbound : ∀ i ∈ I, Finset.sum (f i) (fun n => (1 : ℝ) / n) ≤ δ := by
      intro x hx
      have hxy_pos : 0 < 2 ^ (x : ℝ) * Y := by
        exact mul_pos (Real.rpow_pos_of_pos zero_lt_two _) h0Y
      calc
        Finset.sum (f x) (fun n => (1 : ℝ) / n) ≤ ((f x).card : ℝ) * (1 / (2 ^ (x : ℝ) * Y)) := by
          refine sum_le_card_mul_real ?_
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Ico] at hn
          have hxy_le_n : 2 ^ (x : ℝ) * Y ≤ n := by
            exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn.1.1)
          exact one_div_le_one_div_of_le hxy_pos hxy_le_n
        _ ≤ (δ * (2 ^ (x : ℝ) * Y)) * (1 / (2 ^ (x : ℝ) * Y)) := by
          refine mul_le_mul_of_nonneg_right (h (2 ^ (x : ℝ) * Y) ?_) ?_
          · constructor
            · have hpow1 : (1 : ℝ) ≤ 2 ^ (x : ℝ) := by
                refine one_le_rpow one_le_two ?_
                exact_mod_cast Nat.zero_le x
              exact le_mul_of_one_le_left h0Y.le hpow1
            · rw [Finset.mem_range, Nat.lt_succ_iff] at hx
              have hxlog : (x : ℝ) ≤ Real.logb 2 ((N : ℝ) / Y) := by
                have hx' : (x : ℝ) ≤ ⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ := by
                  exact_mod_cast hx
                refine le_trans hx' ?_
                refine Nat.floor_le ?_
                refine Real.logb_nonneg one_lt_two ?_
                rw [one_le_div h0Y]
                exact hYN
              have hpow_le : (2 : ℝ) ^ (x : ℝ) ≤ (N : ℝ) / Y :=
                (Real.le_logb_iff_rpow_le one_lt_two (div_pos h0N h0Y)).1 hxlog
              exact (_root_.le_div_iff₀ h0Y).mp hpow_le
          · positivity
        _ = δ := by
          have hpow_ne : (2 : ℝ) ^ (x : ℝ) ≠ 0 := by positivity
          have hY_ne : Y ≠ 0 := ne_of_gt h0Y
          field_simp [hpow_ne, hY_ne]
    calc
      Finset.sum I (fun x => Finset.sum (f x) (fun n => (1 : ℝ) / n)) ≤
        Finset.sum I (fun _ => δ) := by
        exact Finset.sum_le_sum fun x hx => hbound x hx
      _ = I.card * δ := by simp [nsmul_eq_mul]
      _ ≤ ((2 / log 2) * log (N : ℝ)) * δ := by
        refine mul_le_mul_of_nonneg_right ?_ h0δ.le
        dsimp [I]
        rw [Finset.card_range]
        push_cast
        have hlogb_nonneg : 0 ≤ Real.logb 2 ((N : ℝ) / Y) := by
          refine Real.logb_nonneg one_lt_two ?_
          rw [one_le_div h0Y]
          exact hYN
        have hlogb_le : Real.logb 2 ((N : ℝ) / Y) ≤ Real.logb 2 (N : ℝ) := by
          exact Real.logb_le_logb_of_le one_lt_two (div_pos h0N h0Y) (div_le_self h0N.le h1Y)
        have hone_le : 1 ≤ Real.logb 2 (N : ℝ) := by
          rw [Real.logb, one_le_div (Real.log_pos one_lt_two)]
          exact log_le_log_of_le zero_lt_two (by exact_mod_cast h2N)
        calc
          (⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ : ℝ) + 1 ≤ Real.logb 2 (N : ℝ) + 1 := by
            simpa [add_comm] using add_le_add_right ((Nat.floor_le hlogb_nonneg).trans hlogb_le) 1
          _ ≤ Real.logb 2 (N : ℝ) + Real.logb 2 (N : ℝ) := by linarith
          _ = (2 / log 2) * log (N : ℝ) := by
            rw [Real.logb, div_eq_mul_inv]
            ring
      _ = (2 / log 2) * δ * log (N : ℝ) := by ring
  · have hempty : Icc ⌈Y⌉₊ N = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact Nat.not_le.mp fun hceil => hYN (Nat.ceil_le.mp hceil)
    suffices hnonneg : (0 : ℝ) ≤ (2 / log 2) * δ * log (N : ℝ) by
      simpa [hempty] using hnonneg
    have hlogNnonneg : 0 ≤ log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (le_trans (show 1 ≤ 2 by norm_num) h2N))
    refine mul_nonneg ?_ hlogNnonneg
    refine mul_nonneg ?_ h0δ.le
    exact div_nonneg zero_le_two (le_of_lt (Real.log_pos one_lt_two))

set_option maxHeartbeats 800000 in
-- This proof needs a larger heartbeat budget because the eventuality/telescoping inequalities
-- trigger expensive normalization and `linarith` search near the end.
lemma harmonic_filter_reg :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n =>
                    n ≠ 0 ∧
                      ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                          (ω n : ℝ) ≤ (3 : ℝ) / 2 * log (log (N : ℝ))))).sum
                (fun n => (1 : ℝ) / n) ≤
              C * log (N : ℝ) / log (log (N : ℝ)))
          atTop := by
  rcases turan_primes_estimate with ⟨C₁, hturan⟩
  rw [Filter.eventually_atTop] at hturan
  rcases hturan with ⟨C₂, hturan⟩
  let C₃ := max C₁ 1
  have h0C₃ : 0 < C₃ := by
    refine lt_of_lt_of_le zero_lt_one ?_
    exact le_max_right _ _
  let c₁ := C₃ * (4 / (1 / 200 : ℝ) ^ 2)
  have h0c₁ : 0 < c₁ := by
    dsimp [c₁]
    refine mul_pos h0C₃ ?_
    refine div_pos zero_lt_four ?_
    positivity
  let C := (c₁ / (198 / 199 : ℝ)) * (2 / log 2)
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos ?_ ?_
    · refine div_pos h0c₁ ?_
      norm_num
    · exact div_pos zero_lt_two (Real.log_pos one_lt_two)
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ eventually_ge_atTop 2
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((C₂ : ℝ) / 2))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop (log 4))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((2 : ℝ) ^ (100 : ℝ)))
    , now_last_large_N ] with
      N h2N hYlarge h1Y h0loglogN h4logN hbiglogN hweird
  let p := fun n : ℕ =>
    n ≠ 0 ∧
      ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
          (ω n : ℝ) ≤ (3 : ℝ) / 2 * log (log (N : ℝ)))
  let Y := (N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))
  let δ := c₁ / ((198 / 199 : ℝ) * log (log (N : ℝ)))
  have h0loglogN' : 0 < log (log (N : ℝ)) := by
    simpa using h0loglogN
  have h0N : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two h2N
  have h0logN : 0 < log (N : ℝ) := by
    refine lt_of_lt_of_le (Real.log_pos one_lt_four) h4logN
  have h0δ : 0 < δ := by
    dsimp [δ]
    refine div_pos h0c₁ ?_
    refine mul_pos ?_ h0loglogN'
    norm_num
  refine le_trans (crude_ps p δ Y h0δ (le_of_lt h1Y) N ?_ h2N) ?_
  · intro X hX
    have h1X : 1 ≤ X := le_trans (le_of_lt h1Y) hX.1
    let M := ⌈2 * X⌉₊
    have h0M : (0 : ℝ) < (M : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr <| by nlinarith [h1X]
    have hM' : (198 / 199 : ℝ) * log (log (N : ℝ)) ≤ log (log (M : ℝ)) := by
      transitivity log (log Y)
      · dsimp [Y]
        rw [Real.log_rpow h0N]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hweird
      · refine log_le_log_of_le ?_ ?_
        · refine Real.log_pos h1Y
        · refine log_le_log_of_le ?_ ?_
          · dsimp [Y]
            exact Real.rpow_pos_of_pos h0N _
          · refine le_trans hX.1 ?_
            dsimp [M]
            refine le_trans ?_ (Nat.le_ceil _)
            refine le_mul_of_one_le_left ?_ ?_
            · linarith
            · norm_num
    have h0loglogM : 0 < log (log (M : ℝ)) := by
      refine lt_of_lt_of_le ?_ hM'
      refine mul_pos ?_ h0loglogN'
      norm_num
    have hMX : (M : ℝ) ≤ 4 * X := by
      dsimp [M]
      refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
      · positivity
      · nlinarith
    have hM'' : log (log (M : ℝ)) ≤ (101 / 100 : ℝ) * log (log (N : ℝ)) := by
      have haux1 : 0 < log (4 * X) := by
        refine Real.log_pos ?_
        refine lt_of_lt_of_le one_lt_four ?_
        refine le_mul_of_one_le_right (show 0 ≤ (4 : ℝ) by positivity) h1X
      have haux2 : 0 < log (4 * (N : ℝ)) := by
        refine lt_of_lt_of_le haux1 ?_
        refine log_le_log_of_le ?_ ?_
        · refine mul_pos zero_lt_four ?_
          linarith
        · nlinarith [hX.2]
      transitivity log (log (4 * X))
      · refine log_le_log_of_le ?_ ?_
        · refine Real.log_pos ?_
          refine lt_of_lt_of_le one_lt_two ?_
          refine le_trans ?_ (Nat.le_ceil _)
          nlinarith
        · refine log_le_log_of_le h0M hMX
      transitivity log (log (4 * (N : ℝ)))
      · refine log_le_log_of_le haux1 ?_
        refine log_le_log_of_le ?_ ?_
        · refine mul_pos zero_lt_four ?_
          linarith
        · nlinarith [hX.2]
      · rw [← Real.log_rpow h0logN]
        refine log_le_log_of_le haux2 ?_
        transitivity (2 : ℝ) * log (N : ℝ)
        · rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h0N), two_mul]
          linarith
        · have hpow : (2 : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) := by
            have h100 : (0 : ℝ) < 100 := by norm_num
            rw [← Real.rpow_le_rpow_iff zero_le_two
                (show 0 ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) by positivity) h100]
            · rw [← Real.rpow_mul h0logN.le]
              rw [show ((1 : ℝ) / 100) * 100 = (1 : ℝ) by norm_num, Real.rpow_one]
              simpa using hbiglogN
          have hmul : 2 * log (N : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) := by
            exact mul_le_mul_of_nonneg_right hpow h0logN.le
          exact
            calc
              2 * log (N : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) := hmul
              _ = log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
              _ = log (N : ℝ) ^ (((1 : ℝ) / 100) + 1) := by
                rw [← Real.rpow_add h0logN]
              _ = log (N : ℝ) ^ ((101 : ℝ) / 100) := by
                rw [show ((1 : ℝ) / 100) + 1 = (101 : ℝ) / 100 by norm_num]
    have hlarge : C₂ ≤ M := by
      dsimp [M]
      rw [← Nat.cast_le (α := ℝ)]
      have hYlarge' : (C₂ : ℝ) / 2 ≤ Y := by
        simpa [Y] using hYlarge
      refine le_trans ?_ (Nat.le_ceil _)
      nlinarith [hYlarge', hX.1]
    have hδM : C₃ * 4 / (1 / 200 : ℝ) ^ 2 ≤ δ * log (log (M : ℝ)) := by
      dsimp [δ, c₁]
      rw [div_mul_eq_mul_div, ← mul_div, mul_div_assoc]
      refine le_mul_of_one_le_right h0c₁.le ?_
      rw [one_le_div]
      · exact hM'
      · refine mul_pos ?_ h0loglogN'
        norm_num
    have hsubset :
        ((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p) ⊆ ((Icc 1 M).filter p) := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnIco, hnp⟩
      rcases Finset.mem_Ico.mp hnIco with ⟨hnl, hnu⟩
      refine Finset.mem_filter.mpr ⟨?_, hnp⟩
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · exact le_trans (by exact_mod_cast (le_trans h1X (Nat.le_ceil X))) hnl
      · dsimp [M]
        exact le_of_lt hnu
    specialize hturan M hlarge
    by_contra h
    rw [not_le] at h
    have h' : δ * X < (((Icc 1 M).filter p).card : ℝ) := by
      exact lt_of_lt_of_le h (by exact_mod_cast Finset.card_le_card hsubset)
    rw [← not_lt] at hturan
    refine hturan ?_
    calc
      C₁ * (M : ℝ) * log (log (M : ℝ)) ≤ C₃ * (M : ℝ) * log (log (M : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h0loglogM.le
        exact mul_le_mul_of_nonneg_right (le_max_left C₁ (1 : ℝ)) h0M.le
      _ ≤ (δ * X) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
        let a : ℝ := 1 / 200
        have ha_nonneg : 0 ≤ a ^ 2 := by positivity
        have hδM' : C₃ * 4 ≤ (δ * log (log (M : ℝ))) * a ^ 2 := by
          have hmult := mul_le_mul_of_nonneg_right hδM ha_nonneg
          have ha_ne : a ^ 2 ≠ 0 := by positivity
          simpa [a, sq, div_eq_mul_inv, ha_ne, mul_assoc, mul_left_comm, mul_comm] using hmult
        have hdesired :
            C₃ * (4 * X) * log (log (M : ℝ)) ≤
              (δ * X) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
          have hmult := mul_le_mul_of_nonneg_right hδM'
            (show 0 ≤ X * log (log (M : ℝ)) by positivity)
          simpa [a, sq, mul_assoc, mul_left_comm, mul_comm] using hmult
        refine le_trans ?_ hdesired
        gcongr
      _ < ((((Icc 1 M).filter p).card : ℝ)) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
        refine mul_lt_mul_of_pos_right h' ?_
        positivity
      _ ≤ ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
        have hconst :
            ((Icc 1 M).filter p).sum (fun _ => (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2)) ≤
              ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨_, hnP⟩
          dsimp [p] at hnP
          rw [not_and_or] at hnP
          rw [sq_le_sq, le_abs, abs_of_pos]
          · rcases hnP.2 with hn1 | hn2
            · right
              rw [neg_sub, le_sub_iff_add_le]
              rw [not_le] at hn1
              have hbound :
                  (99 / 100 : ℝ) * log (log (N : ℝ)) ≤
                    (199 / 200 : ℝ) * log (log (M : ℝ)) := by
                have htmp := mul_le_mul_of_nonneg_left hM' (show 0 ≤ (199 / 200 : ℝ) by norm_num)
                nlinarith
              have homega :
                  (ω n : ℝ) ≤ (199 / 200 : ℝ) * log (log (M : ℝ)) := by
                exact le_trans (le_of_lt hn1) hbound
              nlinarith
            · left
              rw [le_sub_iff_add_le, add_comm, ← one_add_mul]
              rw [not_le] at hn2
              refine le_trans ?_ (le_of_lt hn2)
              have hstep :
                  ((1 : ℝ) + 1 / 200) * log (log (M : ℝ)) ≤
                    ((1 : ℝ) + 1 / 200) * ((101 / 100 : ℝ) * log (log (N : ℝ))) := by
                gcongr
              have hcoef : ((1 : ℝ) + 1 / 200) * (101 / 100 : ℝ) ≤ (3 : ℝ) / 2 := by
                norm_num
              refine hstep.trans ?_
              exact (show
                  ((1 : ℝ) + 1 / 200) * ((101 / 100 : ℝ) * log (log (N : ℝ))) ≤
                    (3 : ℝ) / 2 * log (log (N : ℝ)) by
                  nlinarith)
          · positivity
        calc
          ((((Icc 1 M).filter p).card : ℝ)) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) =
              ((Icc 1 M).filter p).sum (fun _ => (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2)) := by
                simp [nsmul_eq_mul]
          _ ≤ ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := hconst
      _ ≤ (Icc 1 M).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset _ _
        · intro n _ _
          exact sq_nonneg _
  · have hEq :
        (2 / log 2) * δ * log (N : ℝ) = C * log (N : ℝ) / log (log (N : ℝ)) := by
      dsimp [C, δ]
      field_simp [h0loglogN'.ne', (Real.log_pos one_lt_two).ne']
    rw [hEq]

lemma harmonic_filter_div :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n =>
                    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧
                        (d : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 1000))).sum
                (fun n => (1 : ℝ) / n) ≤
              C * log (N : ℝ) / log (log (N : ℝ)))
          atTop := by
  rcases sieve_lemma_prec' with ⟨C₁, c₁, h0C₁, h0c₁, hsieve⟩
  rw [Filter.eventually_atTop] at hsieve
  rcases hsieve with ⟨C₂, hsieve⟩
  let c₂ := C₁ * (4 * (log 4 / ((1 : ℝ) / 1000)))
  have h0c₂ : 0 < c₂ := by
    dsimp [c₂]
    refine mul_pos h0C₁ ?_
    refine mul_pos zero_lt_four ?_
    exact div_pos (Real.log_pos one_lt_four) (by norm_num)
  let C := c₂ * (2 / log 2)
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos h0c₂ ?_
    exact div_pos zero_lt_two (Real.log_pos one_lt_two)
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ eventually_ge_atTop 2
    , tendsto_natCast_atTop_atTop.eventually (how_large_can_we_go c₁ h0c₁)
    , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((C₂ : ℝ) / 2))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)) ] with
      N h2N hNlarge h1logN hYlarge h1Y
  have h0N : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two h2N
  have h0loglogN : 0 < log (log (N : ℝ)) := Real.log_pos h1logN
  have h0logN : 0 < log (N : ℝ) := lt_trans zero_lt_one h1logN
  let Y := (N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))
  let δ := c₂ / log (log (N : ℝ))
  have h0δ : 0 < δ := by
    dsimp [δ]
    exact div_pos h0c₂ h0loglogN
  let p := fun n =>
    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 1000)
  refine le_trans (crude_ps p δ Y h0δ h1Y N ?_ h2N) ?_
  · intro X hX
    have h1X : 1 ≤ X := le_trans h1Y hX.1
    let M := ⌈2 * X⌉₊
    have hlarge : C₂ ≤ ⌈2 * X⌉₊ := by
      rw [← Nat.cast_le (α := ℝ)]
      refine le_trans ?_ (Nat.le_ceil _)
      rw [mul_comm, ← div_le_iff₀ zero_lt_two]
      exact le_trans hYlarge hX.1
    let y : ℝ := 4
    let z := log (N : ℝ) ^ ((1 : ℝ) / 1000)
    have h2y : (2 : ℝ) ≤ y := by
      norm_num [y]
    have h1z : 1 < z := by
      dsimp [z]
      refine one_lt_rpow h1logN ?_
      norm_num
    have hzM : z ≤ c₁ * log (M : ℝ) := by
      have hzY : z ≤ c₁ * log Y := by
        dsimp [z, Y]
        rw [Real.log_rpow h0N]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hNlarge
      have h0Y : 0 < Y := by
        dsimp [Y]
        exact Real.rpow_pos_of_pos h0N _
      have hX_le_M : X ≤ (M : ℝ) := by
        dsimp [M]
        refine le_trans ?_ (Nat.le_ceil _)
        nlinarith [h1X]
      have hY_le_M : Y ≤ (M : ℝ) := le_trans hX.1 hX_le_M
      have hlogY_le : log Y ≤ log (M : ℝ) := Real.log_le_log h0Y hY_le_M
      exact le_trans hzY (mul_le_mul_of_nonneg_left hlogY_le h0c₁.le)
    have hMX : (M : ℝ) ≤ 4 * X := by
      dsimp [M]
      refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
      · positivity
      · linarith
    have hsubset :
        ((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p) ⊆
          (range M).filter fun n =>
            ∀ q : ℕ, Nat.Prime q → q ∣ n → (q : ℝ) < y ∨ z < q := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range]
      rw [Finset.mem_filter, Finset.mem_Ico] at hn
      refine ⟨hn.1.2, ?_⟩
      intro q hq₁ hq₂
      have hpred : ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ z := hn.2
      rw [not_exists] at hpred
      by_cases hq4 : 4 ≤ q
      · right
        have hqz : ¬ (q : ℝ) ≤ z := by
          exact fun hqz => hpred q ⟨hq₂, hq4, hqz⟩
        exact lt_of_not_ge hqz
      · left
        have hq' : (q : ℝ) < 4 := by
          exact_mod_cast lt_of_not_ge hq4
        simpa [y] using hq'
    specialize hsieve M hlarge y z h2y h1z hzM
    transitivity ((((range M).filter fun n =>
        ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ))
    · exact_mod_cast Finset.card_le_card hsubset
    · refine le_trans hsieve ?_
      have hcoeff_nonneg : 0 ≤ C₁ * (log y / log z) := by
        refine mul_nonneg h0C₁.le ?_
        refine div_nonneg ?_ (le_of_lt (Real.log_pos h1z))
        exact Real.log_nonneg (le_trans one_le_two h2y)
      have hcoeff_eq : C₁ * (log y / log z) * 4 = δ := by
        dsimp [δ, c₂, z, y]
        have h1000 : ((1 : ℝ) / 1000) ≠ 0 := by norm_num
        rw [Real.log_rpow h0logN]
        field_simp [h0loglogN.ne', h1000]
      calc
        C₁ * (log y / log z) * (M : ℝ) ≤ C₁ * (log y / log z) * (4 * X) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hMX hcoeff_nonneg
        _ = (C₁ * (log y / log z) * 4) * X := by ring
        _ = δ * X := by rw [hcoeff_eq]
  · have hEq : (2 / log 2) * δ * log (N : ℝ) = C * log (N : ℝ) / log (log (N : ℝ)) := by
      dsimp [C, δ]
      field_simp [h0loglogN.ne', (Real.log_pos one_lt_two).ne']
    rw [hEq]

lemma harmonic_filter_smooth_h1M {N : ℕ}
    (hN₁ : (1 : ℝ) < N) :
    1 ≤ ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊ := by
  refine Nat.succ_le_of_lt (Nat.ceil_pos.mpr ?_)
  exact Real.rpow_pos_of_pos (lt_trans zero_lt_one hN₁) _

lemma harmonic_filter_smooth_hMN {N : ℕ}
    (hN₁ : (1 : ℝ) < N)
    (h0loglogN : 0 < log (log (N : ℝ))) :
    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ N := by
  have h1N : (1 : ℝ) ≤ N := le_of_lt hN₁
  calc
    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ (N : ℝ) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le h1N ?_
      have hnonneg : 0 ≤ 8 / log (log (N : ℝ)) := by
        positivity
      linarith
    _ = N := by simp

lemma harmonic_filter_smooth_hcomp {N : ℕ}
    (hN₁ : (1 : ℝ) < N)
    (h16loglogN : 16 ≤ log (log (N : ℝ))) :
    log (log (N : ℝ)) ≤ log ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))) := by
  have h0N : 0 < (N : ℝ) := by
    exact lt_trans zero_lt_one hN₁
  have h0logN : 0 < log (N : ℝ) := Real.log_pos hN₁
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  rw [Real.log_rpow h0N]
  have hlogN_ge4 : (4 : ℝ) ≤ log (N : ℝ) := by
    have htmp : Real.exp 4 ≤ Real.exp (log (log (N : ℝ))) := by
      exact Real.exp_le_exp.mpr (le_trans (by norm_num) h16loglogN)
    have h4le : (4 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp 4]
    exact le_trans h4le (by simpa [Real.exp_log h0logN] using htmp)
  have h1logN : (1 : ℝ) ≤ log (N : ℝ) := by
    linarith
  have hloglog_le_sqrt :
      log (log (N : ℝ)) ≤ (log (N : ℝ)) ^ (1 / 2 : ℝ) := by
    refine le_trans (log_le_thing (x := log (N : ℝ)) h1logN) ?_
    exact sub_le_self _ (by positivity)
  have hsqrt_sq : ((log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = log (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0logN.le]
    norm_num
  have hsqrt_le_halflog : (log (N : ℝ)) ^ (1 / 2 : ℝ) ≤ log (N : ℝ) / 2 := by
    have hsq_nonneg : 0 ≤ (((log (N : ℝ)) ^ (1 / 2 : ℝ)) - 2) ^ 2 := sq_nonneg _
    nlinarith
  have hloglog_le_halflog : log (log (N : ℝ)) ≤ log (N : ℝ) / 2 := by
    exact le_trans hloglog_le_sqrt hsqrt_le_halflog
  have h8div_le_half : 8 / log (log (N : ℝ)) ≤ (1 / 2 : ℝ) := by
    field_simp [h0loglogN.ne']
    linarith
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 8 / log (log (N : ℝ)) := by
    linarith
  have hhalflog_le :
      log (N : ℝ) / 2 ≤ ((1 : ℝ) - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hhalf_le h0logN.le
  exact le_trans hloglog_le_halflog hhalflog_le

lemma harmonic_filter_smooth_hNqrec {N q : ℕ} {C₂ : ℝ}
    (hharmonic :
      ∀ N : ℝ, 1 ≤ N → (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n) ≤ C₂ * log (2 * N))
    (hq0 : 0 < q)
    (hqN : q ≤ N) :
    (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹) := by
  let g : ℕ → ℕ := fun m => m / q
  transitivity (Finset.sum (Icc 1 ⌊(N : ℝ) / q⌋₊) (fun m => (1 : ℝ) / (m * q)))
  · refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
    · intro m hm
      rw [one_div_nonneg]
      positivity
    · intro n hn
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Nat.succ_le_iff]
      refine ⟨Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn.1.1) hn.2) hq0, ?_⟩
      refine Nat.le_floor ?_
      rw [Nat.cast_div hn.2]
      · refine (div_le_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq0)).2 ?_
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
        simpa [div_mul_cancel₀ _ hqR] using (show (n : ℝ) ≤ N by exact_mod_cast hn.1.2)
      · exact_mod_cast hq0.ne'
    · intro a₁ ha₁ a₂ ha₂ ha
      rw [Finset.mem_filter] at ha₁ ha₂
      exact (Nat.div_left_inj ha₁.2 ha₂.2).1 ha
    · intro n hn
      rw [Finset.mem_filter] at hn
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      rw [Nat.cast_div hn.2 hqR]
      rw [div_mul_cancel₀ _ hqR]
  · transitivity ((1 : ℝ) / q * Finset.sum (Icc 1 ⌊(N : ℝ) / q⌋₊) (fun m => (1 : ℝ) / m))
    · rw [Finset.mul_sum]
      refine le_of_eq ?_
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [one_div, mul_comm]
    · have h :=
        mul_le_mul_of_nonneg_left
          (hharmonic ((N : ℝ) / q) ?_)
          (by positivity : 0 ≤ (1 : ℝ) / q)
      · simpa [one_div, mul_comm] using h
      · rw [le_div_iff₀]
        · simpa [one_mul] using (show (q : ℝ) ≤ N by exact_mod_cast hqN)
        · exact_mod_cast hq0

lemma harmonic_filter_smooth_hNqrec' {N : ℕ} {M C₂ : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h0C₂ : 0 < C₂)
    (hweird : C₂ * log 2 ≤ log (N : ℝ) / log (log (N : ℝ)))
    (hNqrec :
      ∀ q : ℕ,
        0 < q →
          q ≤ N →
            (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
              C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹)) :
    ∀ q ∈ ((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q),
      (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
        (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹) := by
  intro q hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  have hq0 : 0 < q := hq.2.1.pos
  have h0N : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le hq0 hq.1.2
  have h0M : 0 < M := by
    rw [hM]
    exact Real.rpow_pos_of_pos h0N _
  refine le_trans (hNqrec q hq0 hq.1.2) ?_
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr <| Nat.cast_nonneg q)
  transitivity C₂ * log (2 * ((N : ℝ) / M))
  · refine mul_le_mul_of_nonneg_left ?_ h0C₂.le
    refine Real.log_le_log ?_ ?_
    · refine mul_pos zero_lt_two (div_pos h0N ?_)
      exact_mod_cast hq0
    · refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ h0N.le
      simpa [one_div] using one_div_le_one_div_of_le h0M (by exact_mod_cast le_of_lt hq.2.2)
  · rw [hM, Real.log_mul (by norm_num) (by positivity), mul_add, add_mul, add_comm]
    refine add_le_add ?_ ?_
    · refine le_of_eq ?_
      rw [div_eq_mul_inv, ← Real.rpow_neg h0N.le, mul_comm (N : ℝ), ← Real.rpow_add_one h0N.ne' _,
        neg_sub, sub_add, sub_self, sub_zero, Real.log_rpow h0N]
      ring_nf
    · rw [one_mul]
      exact hweird

lemma harmonic_filter_smooth_htail {N : ℕ} {M b c C C₂ : ℝ}
    (hC : 2 * c ≤ C / (8 * C₂ + 1) - 2 * 8)
    (h0c : 0 < c)
    (h0C₂ : 0 < C₂)
    (h8loglogN : 8 < log (log (N : ℝ)))
    (h16loglogN : 16 ≤ log (log (N : ℝ)))
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h0logN : 0 < log (N : ℝ))
    (h0logM : 0 < log M)
    (hcomp : log (log (N : ℝ)) ≤ log M)
    (hmertensN :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹)
    (hmertensM :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹) :
    Finset.sum ((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q)
        (fun q => (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹)) ≤
      C * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
  let Q : Finset ℕ := (Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q
  let A : Finset ℕ := (Finset.Icc 1 N).filter IsPrimePow
  let B : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst hN0
    norm_num at h0logN
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have h1N : (1 : ℝ) < N := by
    by_contra hN
    have hexp : Real.exp (0 : ℝ) < Real.exp (log (N : ℝ)) := by
      exact Real.exp_lt_exp.mpr h0logN
    have hNgt : (1 : ℝ) < N := by
      simpa [Real.exp_zero, Real.exp_log h0N] using hexp
    exact hN hNgt
  have hloglogN' : 0 < 1 - 8 / log (log (N : ℝ)) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  have h0M : 0 < M := by
    rw [hM]
    exact Real.rpow_pos_of_pos h0N _
  have hMN : M ≤ N := by
    rw [hM]
    exact harmonic_filter_smooth_hMN (N := N) h1N h0loglogN
  have hfloorMN : ⌊M⌋₊ ≤ N := by
    simpa [Nat.floor_natCast] using nat_floor_real_le_floor (N := N) hMN
  have hQaux : Q ⊆ A \ B := by
    intro q hq
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, not_and, Finset.mem_Icc]
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    refine ⟨⟨⟨?_, hq.1.2⟩, hq.2.1⟩, ?_⟩
    · exact le_trans one_le_two (IsPrimePow.two_le hq.2.1)
    · intro hqB hqpp
      rw [Finset.mem_Icc] at hqB
      have hfloorMltq : ⌊M⌋₊ < q := by
        exact (Nat.floor_lt' (Nat.ne_of_gt hqpp.pos)).2 (by simpa using hq.2.2)
      exact not_lt_of_ge hqB.2 hfloorMltq
  have hBsubA : B ⊆ A := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqpp⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hq2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans hq2 hfloorMN⟩, hqpp⟩
  have hsum_subset :
      Finset.sum Q (fun q => (q : ℝ)⁻¹) ≤ Finset.sum (A \ B) (fun q => (q : ℝ)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hQaux ?_
    intro q _hq _hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg q)
  have hsumN :
      Finset.sum A (fun q => (q : ℝ)⁻¹) ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) := by
    have htmp := sub_le_of_abs_sub_le_right hmertensN
    simpa [A, add_assoc, add_left_comm, add_comm] using htmp
  have hsumM :
      -(c * |log M|⁻¹) + (log (log M) + b) ≤ Finset.sum B (fun q => (q : ℝ)⁻¹) := by
    have htmp := sub_le_of_abs_sub_le_left hmertensM
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, B] using htmp
  have hlogM_eq : log M = (1 - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    rw [hM, Real.log_rpow h0N]
  have hloglogM_eq :
      log (log M) = log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) := by
    rw [hlogM_eq, Real.log_mul hloglogN'.ne' h0logN.ne']
  have hInvN_le_logM : (log (N : ℝ))⁻¹ ≤ (log M)⁻¹ := by
    have hlogM_le_logN : log M ≤ log (N : ℝ) := log_le_log_of_le h0M hMN
    simpa [one_div] using one_div_le_one_div_of_le h0logM hlogM_le_logN
  have hInvM_le_loglogN : (log M)⁻¹ ≤ (log (log (N : ℝ)))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le h0loglogN hcomp
  have hInvN_le_loglogN : (log (N : ℝ))⁻¹ ≤ (log (log (N : ℝ)))⁻¹ := by
    exact le_trans hInvN_le_logM hInvM_le_loglogN
  have hbound_inv :
      c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ ≤ 2 * c / log (log (N : ℝ)) := by
    rw [abs_of_pos h0logN, abs_of_pos h0logM]
    have h1 : c * (log (N : ℝ))⁻¹ ≤ c * (log (log (N : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hInvN_le_loglogN h0c.le
    have h2 : c * (log M)⁻¹ ≤ c * (log (log (N : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hInvM_le_loglogN h0c.le
    calc
      c * (log (N : ℝ))⁻¹ + c * (log M)⁻¹
          ≤ c * (log (log (N : ℝ)))⁻¹ + c * (log (log (N : ℝ)))⁻¹ := by
            exact add_le_add h1 h2
      _ = 2 * c / log (log (N : ℝ)) := by
            field_simp [h0loglogN.ne']
            norm_num
  have hy_half : 8 / log (log (N : ℝ)) ≤ (1 / 2 : ℝ) := by
    field_simp [h0loglogN.ne']
    linarith
  have hloghelper :
      -(2 * (8 / log (log (N : ℝ)))) ≤ log (1 - 8 / log (log (N : ℝ))) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using log_helper (8 / log (log (N : ℝ))) (by positivity) hy_half
  have hbound_log :
      log (log (N : ℝ)) - log (log M) ≤ 16 / log (log (N : ℝ)) := by
    rw [hloglogM_eq]
    ring_nf
    have hneg' := neg_le_neg hloghelper
    ring_nf at hneg'
    exact hneg'
  have hdenpos : 0 < 8 * C₂ + 1 := by
    nlinarith
  have hC' : (2 * c + 16) * (8 * C₂ + 1) ≤ C := by
    have hCtemp := hC
    rw [le_sub_iff_add_le, _root_.le_div_iff₀ hdenpos] at hCtemp
    norm_num at hCtemp ⊢
    exact hCtemp
  have htail_inv :
      Finset.sum Q (fun q => (q : ℝ)⁻¹) ≤ (2 * c + 16) / log (log (N : ℝ)) := by
    refine le_trans hsum_subset ?_
    calc
      Finset.sum (A \ B) (fun q => (q : ℝ)⁻¹)
          = Finset.sum A (fun q => (q : ℝ)⁻¹) - Finset.sum B (fun q => (q : ℝ)⁻¹) := by
            exact Finset.sum_sdiff_eq_sub hBsubA
      _ ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) - Finset.sum B (fun q => (q : ℝ)⁻¹) := by
            exact sub_le_sub_right hsumN _
      _ ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
            (-(c * |log M|⁻¹) + (log (log M) + b)) := by
            exact sub_le_sub_left hsumM _
      _ ≤ (2 * c + 16) / log (log (N : ℝ)) := by
            have hmain :
                c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
                    (-(c * |log M|⁻¹) + (log (log M) + b)) =
                  c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ +
                    (log (log (N : ℝ)) - log (log M)) := by
              ring
            rw [hmain]
            calc
              c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ + (log (log (N : ℝ)) - log (log M))
                  ≤ 2 * c / log (log (N : ℝ)) + 16 / log (log (N : ℝ)) := by
                    exact add_le_add hbound_inv hbound_log
              _ = (2 * c + 16) / log (log (N : ℝ)) := by
                    field_simp [h0loglogN.ne']
  have hcoeff_nonneg : 0 ≤ (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) := by
    refine mul_nonneg ?_ ?_
    · linarith
    · exact div_nonneg h0logN.le h0loglogN.le
  calc
    Finset.sum Q (fun q => (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹))
        = ((8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ)))) *
            Finset.sum Q (fun q => (q : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
    _ ≤ ((8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ)))) *
          ((2 * c + 16) / log (log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left htail_inv hcoeff_nonneg
    _ = ((2 * c + 16) * (8 * C₂ + 1)) * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
          field_simp [h0loglogN.ne']
    _ ≤ C * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
          have hnonneg : 0 ≤ log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by positivity
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hC' hnonneg

lemma harmonic_filter_smooth_hstep1 {N : ℕ} {M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h1M : 1 ≤ ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊) :
    ((Finset.Icc ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊ N).filter
          (fun n : ℕ =>
            ∃ q : ℕ,
              IsPrimePow q ∧
                ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n))).sum
        (fun m => (1 : ℝ) / m) ≤
      ((((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q).biUnion
            fun q => (Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum
          fun n => (1 : ℝ) / n) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn.2 with ⟨q, hqpp, hMq, hqdiv⟩
    have hn1 : 1 ≤ n := le_trans h1M hn.1.1
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨q, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le q, ?_⟩, ⟨hqpp, ?_⟩⟩
      · exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqdiv) hn.1.2
      · simpa [hM] using hMq
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨le_trans h1M hn.1.1, hn.1.2⟩, hqdiv⟩
  · intro m hm₁ hm₂
    exact one_div_nonneg.mpr (Nat.cast_nonneg m)

lemma harmonic_filter_smooth :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (1 - 1 / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n : ℕ =>
                    ∃ q : ℕ,
                      IsPrimePow q ∧
                        ((N : ℝ) ^ (1 - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n))).sum
                (fun m => (1 : ℝ) / m) ≤
              C * log (N : ℝ) / log (log (N : ℝ)) ^ 2)
          atTop := by
  have hlogpow :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound (show 0 < (1 : ℝ) by norm_num)
  obtain ⟨b, hmertens₀⟩ := prime_power_reciprocal
  obtain ⟨c, h0c, hmertens⟩ := hmertens₀.exists_pos
  obtain ⟨C₂, h0C₂, hharmonic⟩ := harmonic_sum_bound'
  let C : ℝ := max ((2 * c + 2 * 8) * (8 * C₂ + 1)) 1
  have h0C : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 2 * c ≤ C / (8 * C₂ + 1) - 2 * 8 := by
    have hden : 0 < 8 * C₂ + 1 := by
      refine add_pos ?_ zero_lt_one
      refine mul_pos ?_ h0C₂
      norm_num
    rw [le_sub_iff_add_le, _root_.le_div_iff₀ hden]
    exact le_max_left _ _
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ (another_this_particular_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (C₂ * log 2))
    , tendsto_natCast_atTop_atTop.eventually hlogpow
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , tendsto_log_log_coe_at_top (eventually_ge_atTop (16 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually hmertens.bound
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually
        hmertens.bound ] with
    N hweird hNlogpow hN₁ hM₁ h16loglogN hmertensN hmertensM
  have h1N : (1 : ℝ) ≤ N := le_of_lt hN₁
  have h0N : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one h1N
  have h0logN : 0 < log N := Real.log_pos hN₁
  have h8loglogN : 8 < log (log N) := lt_of_lt_of_le (by norm_num) h16loglogN
  have h0loglogN : 0 < log (log N) := lt_of_lt_of_le (by norm_num) h16loglogN
  have hloglogN' : 0 < 1 - 8 / log (log N) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  let M : ℝ := N ^ (1 - 8 / log (log N))
  have h1M : 1 ≤ ⌈(N : ℝ) ^ (1 - 1 / log (log N))⌉₊ := by
    exact harmonic_filter_smooth_h1M (N := N) hN₁
  have h0logM : 0 < log M := Real.log_pos hM₁
  have h0M : 0 < M := by
    dsimp [M]
    exact Real.rpow_pos_of_pos h0N _
  have hMN : M ≤ N := by
    change (N : ℝ) ^ ((1 : ℝ) - 8 / log (log N)) ≤ N
    exact harmonic_filter_smooth_hMN (N := N) hN₁ h0loglogN
  have hcomp : log (log N) ≤ log M := by
    change log (log N) ≤ log ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log N)))
    exact harmonic_filter_smooth_hcomp (N := N) hN₁ h16loglogN
  have hmertensN' :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹ := by
    simpa [Nat.floor_natCast, norm_inv, norm_eq_abs] using hmertensN
  have hmertensM' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹ := by
    simpa [M, norm_inv, norm_eq_abs] using hmertensM
  let Q : Finset ℕ := (Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q
  let Nq : ℕ → Finset ℕ := fun q => (Icc 1 N).filter fun n : ℕ => q ∣ n
  have hNqrec :
      ∀ q : ℕ,
        0 < q →
          q ≤ N →
            (Nq q).sum (fun n => (1 : ℝ) / n) ≤
              C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹) := by
    intro q hq0 hqN
    change (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹)
    exact harmonic_filter_smooth_hNqrec (N := N) (q := q) (C₂ := C₂) hharmonic hq0 hqN
  have hNqrec' :
      ∀ q ∈ Q,
        (Nq q).sum (fun n => (1 : ℝ) / n) ≤
          (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹) := by
    intro q hq
    change (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)
    exact
      harmonic_filter_smooth_hNqrec' (N := N) (M := M) (C₂ := C₂) rfl h0C₂ hweird hNqrec q
        (by simpa [Q] using hq)
  have htail :
      Finset.sum Q (fun q => (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)) ≤
        C * log N / log (log N) ^ 2 := by
    simpa [Q] using
      harmonic_filter_smooth_htail (N := N) (M := M) (b := b) (c := c) (C := C) (C₂ := C₂)
        hC h0c h0C₂ h8loglogN h16loglogN rfl h0logN h0logM hcomp hmertensN' hmertensM'
  calc
    ((Icc ⌈(N : ℝ) ^ (1 - 1 / log (log N))⌉₊ N).filter
          (fun n : ℕ =>
            ∃ q : ℕ, IsPrimePow q ∧ ((N : ℝ) ^ (1 - 8 / log (log N)) < (q : ℝ) ∧ q ∣ n))).sum
        (fun m => (1 : ℝ) / m)
        ≤ (Q.biUnion fun q => Nq q).sum (fun n => (1 : ℝ) / n) := by
          simpa [Q, Nq, M] using harmonic_filter_smooth_hstep1 (N := N) (M := M) rfl h1M
    _ ≤ Finset.sum Q (fun q => Finset.sum (Nq q) (fun n => (1 : ℝ) / n)) := by
          exact sum_bUnion_le_sum_of_nonneg (by
            intro n hn
            exact one_div_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ Finset.sum Q (fun q => (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact hNqrec' q hq
    _ ≤ C * log N / log (log N) ^ 2 := htail
end UnitFractions
