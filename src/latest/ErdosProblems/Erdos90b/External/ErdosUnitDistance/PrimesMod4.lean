/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import PrimeNumberTheoremAnd.Consequences

/-!
# Primes in the progressions 1, 3 mod 4

The `j`-th primes `≡ 1, 3 (mod 4)`, their polynomial growth (from
PrimeNumberTheoremAnd's `chebyshev_asymptotic_pnt`), and the product
`m t` of the first `t` primes `≡ 1 (mod 4)`.
-/

open scoped Classical
open Filter

namespace Erdos

/-- If eventually `count p x ≥ x / (4 log x)`, then eventually
`nth p j ≤ (j+2)²`.  (Key step: at `x = (j+2)²` the hypothesis gives
`count p x ≥ (j+2)²/(8 log (j+2)) > j` for large `j`, using
`log y ≤ 2√y`; conclude with `Nat.nth_lt_of_lt_count`.) -/
theorem nth_le_sq_of_count_ge (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ᶠ x : ℕ in atTop, (x : ℝ) / (4 * Real.log x) ≤ Nat.count p x) :
    ∀ᶠ j : ℕ in atTop, (Nat.nth p j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by
  have hx : Tendsto (fun j : ℕ => (j + 2) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id_eq]; nlinarith) tendsto_id
  filter_upwards [hx.eventually h, eventually_ge_atTop 255] with j hcount hj
  set y : ℝ := (j : ℝ) + 2 with hy
  have hy257 : (257 : ℝ) ≤ y := by
    have : (255 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    simp only [hy]; linarith
  have hyx : (((j + 2) ^ 2 : ℕ) : ℝ) = y ^ 2 := by push_cast; ring
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hs16 : (16 : ℝ) ≤ Real.sqrt y := by
    have : (16 : ℝ) = Real.sqrt 256 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogy : Real.log y ≤ 2 * Real.sqrt y := by
    have hsq : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (by nlinarith)
    have hls : Real.log (Real.sqrt y) = Real.log y / 2 :=
      Real.log_sqrt (by linarith)
    linarith [hls ▸ hsq]
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  -- the hypothesis at x = (j+2)²
  have hcount' : y ^ 2 / (8 * Real.log y) ≤ (Nat.count p ((j + 2) ^ 2) : ℝ) := by
    have hlog : Real.log (((j + 2) ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
      rw [hyx, show y ^ 2 = y * y by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [hlog, hyx] at hcount
    calc y ^ 2 / (8 * Real.log y) = y ^ 2 / (4 * (2 * Real.log y)) := by ring_nf
    _ ≤ _ := hcount
  -- conclude j < count
  have h8 : 8 * Real.log y ≤ y := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.sqrt y - 16 by linarith) hs0]
  have hjy : (j : ℝ) < y ^ 2 / (8 * Real.log y) := by
    rw [lt_div_iff₀ (by positivity)]
    have hjlt : (j : ℝ) < y := by rw [hy]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
      mul_lt_mul_of_pos_right hjlt (show (0 : ℝ) < y by linarith)]
  have hjc : j < Nat.count p ((j + 2) ^ 2) := by
    have : (j : ℝ) < (Nat.count p ((j + 2) ^ 2) : ℝ) := lt_of_lt_of_le hjy hcount'
    exact_mod_cast this
  have hnth : Nat.nth p j < (j + 2) ^ 2 := Nat.nth_lt_of_lt_count hjc
  calc (Nat.nth p j : ℝ) ≤ (((j + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnth.le
  _ = y ^ 2 := hyx

/-- The `j`-th prime congruent to `3` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

/-- The `i`-th prime congruent to `1` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i

/-- Chebyshev-type counting lower bound in a primitive class mod 4:
eventually `#{p < x : p prime, p ≡ a mod 4} ≥ x / (4 log x)`.
Sketch: `chebyshev_asymptotic_pnt` gives
`S x := ∑_{p ≤ ⌊x⌋, p ≡ a (4)} log p ~ x/2`, so eventually `S x ≥ 2x/5`;
each summand is at most `log x` and the number of nonzero summands among
`p ≤ n - 1` is `Nat.count _ n`, so
`count n ≥ S (n-1) / log n ≥ (2(n-1)/5) / log n ≥ n / (4 log n)`. -/
theorem count_mod_four_ge {a : ℕ} (ha : a = 1 ∨ a = 3) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (4 * Real.log x) ≤ Nat.count (fun n => n.Prime ∧ n % 4 = a) x := by
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ Finset.Iic ⌊x⌋₊ with Nat.Prime p, if p % 4 = a then Real.log (p : ℝ) else 0
  have hcheb : Asymptotics.IsEquivalent Filter.atTop S
      (fun x : ℝ => x / (Nat.totient 4 : ℝ)) := by
    exact chebyshev_asymptotic_pnt (by norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
  have hSreal : ∀ᶠ x : ℝ in atTop, (2 / 5 : ℝ) * x ≤ S x := by
    have hne : ∀ᶠ x : ℝ in atTop, x / (Nat.totient 4 : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      norm_num [hx0]
    have ht : Tendsto (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) atTop
        (nhds (1 : ℝ)) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hcheb
    have hratio : ∀ᶠ x : ℝ in atTop,
        (4 / 5 : ℝ) < (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) x :=
      ht.eventually
        (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi (4 / 5 : ℝ) by norm_num))
    filter_upwards [hratio, eventually_ge_atTop (1 : ℝ)] with x hxratio hxge
    have hden : 0 < x / (Nat.totient 4 : ℝ) := by
      have htot : (Nat.totient 4 : ℝ) = 2 := by
        norm_num [show Nat.totient 4 = 2 by decide]
      rw [htot]
      linarith
    have hlt : (4 / 5 : ℝ) * (x / (Nat.totient 4 : ℝ)) < S x := by
      have := (lt_div_iff₀ hden).mp hxratio
      simpa [Pi.div_apply] using this
    have htot : (Nat.totient 4 : ℝ) = 2 := by
      norm_num [show Nat.totient 4 = 2 by decide]
    rw [htot] at hlt
    norm_num at hlt
    linarith
  have hSnat : ∀ᶠ n : ℕ in atTop, (2 / 5 : ℝ) * (n : ℝ) ≤ S n :=
    tendsto_natCast_atTop_atTop.eventually hSreal
  have hsucc : ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) / (4 * Real.log ((n + 1 : ℕ) : ℝ)) ≤
        Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) := by
    filter_upwards [hSnat, eventually_ge_atTop 2] with n hS hn
    have hsum_eq :
        S n =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ) := by
      change
        (∑ p ∈ Finset.Iic ⌊(n : ℝ)⌋₊ with Nat.Prime p,
            if p % 4 = a then Real.log (p : ℝ) else 0) =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ)
      rw [Nat.floor_natCast]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp [and_assoc]
      · intro x hx
        rfl
    have hsum_le :
        S n ≤
          (Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) : ℝ) *
            Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [hsum_eq, Nat.count_eq_card_filter_range]
      have hsum := Finset.sum_le_card_nsmul
        ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a))
        (fun p => Real.log (p : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) ?_
      simpa [nsmul_eq_mul] using hsum
      intro p hp
      have hpmem : p ∈ Finset.range (n + 1) ∧ (p.Prime ∧ p % 4 = a) := by
        simpa using hp
      have hpr : p.Prime := hpmem.2.1
      have hple : p ≤ n := Nat.lt_succ_iff.mp (by simpa using hpmem.1)
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      exact Real.log_le_log hp_pos (by exact_mod_cast Nat.le_trans hple (Nat.le_succ n))
    have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    rw [div_le_iff₀ (mul_pos (by norm_num) hlogpos)]
    have hnum : ((n + 1 : ℕ) : ℝ) / 4 ≤ (2 / 5 : ℝ) * (n : ℝ) := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith
    nlinarith [hnum, hS, hsum_le]
  rcases Filter.eventually_atTop.mp hsucc with ⟨N, hN⟩
  refine Filter.eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro x hx
  have hxpos : 0 < x := by omega
  have hNx : N ≤ x - 1 := by omega
  have hx' := hN (x - 1) hNx
  have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
  simpa [hxsub] using hx'

/-- Eventually the `j`-th prime `≡ 3 mod 4` is at most `(j+2)²`. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inr rfl))

/-- Eventually the `i`-th prime `≡ 1 mod 4` is at most `(i+2)²`. -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ ((i : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inl rfl))

/-! ## Primes in the progressions `1, 3 mod 4` -/

/-- The product `m t = p1 0 * p1 1 * ⋯ * p1 (t-1)` of the first `t` primes
congruent to `1 mod 4`; the repeated unit distance will be (a rescaling of)
a norm-one element above `m t`. -/
noncomputable def m (t : ℕ) : ℕ := ∏ i ∈ Finset.range t, p1 i

/-- [easy] There are infinitely many primes `≡ 3 mod 4`.  Sketch: in
Mathlib as a special case of Dirichlet
(`Nat.forall_exists_prime_gt_and_modEq`), or by the classical elementary
argument. -/
theorem infinite_setOf_q3 : {n | n.Prime ∧ n % 4 = 3}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_and_modEq (by norm_num) (by decide)
  convert! h using 2 with n


/-- [easy] There are infinitely many primes `≡ 1 mod 4`.
(Proved by Aristotle, 2026-06-11.) -/
theorem infinite_setOf_p1 : {n | n.Prime ∧ n % 4 = 1}.Infinite :=
  Nat.infinite_setOf_prime_modEq_one <| by decide

/-- [easy given infinitude] `q3 j` is prime and `≡ 3 mod 4`
(`Nat.nth_mem_of_infinite`). -/
theorem q3_spec (j : ℕ) : (q3 j).Prime ∧ q3 j % 4 = 3 :=
  Nat.nth_mem_of_infinite infinite_setOf_q3 j

/-- [easy given infinitude] `p1 i` is prime and `≡ 1 mod 4`. -/
theorem p1_spec (i : ℕ) : (p1 i).Prime ∧ p1 i % 4 = 1 :=
  Nat.nth_mem_of_infinite infinite_setOf_p1 i

theorem q3_strictMono : StrictMono q3 :=
  Nat.nth_strictMono infinite_setOf_q3

theorem p1_strictMono : StrictMono p1 :=
  Nat.nth_strictMono infinite_setOf_p1

/-- [easy] `m t ≥ 2^t` (each prime factor is `≥ 5`). -/
theorem m_ge (t : ℕ) : 2 ^ t ≤ m t := by
  calc 2 ^ t = ∏ _i ∈ Finset.range t, 2 := by simp
  _ ≤ m t := Finset.prod_le_prod' fun i _ => (p1_spec i).1.two_le

/-- [medium given `p1_poly_bound`] The logarithm of `m t` grows like
`t log t` up to constants: there is `c₁ ≥ 1` with
`log (m t) ≤ c₁ * t * log (t + 2)` for all `t`.  Sketch:
`log (m t) = ∑_{i<t} log (p1 i)`; bound all but finitely many summands by
`2 log (i + 2) ≤ 2 log (t + 2)` using `p1_poly_bound` and absorb the
finitely many exceptions into `c₁`. -/
theorem log_m_le : ∃ c₁ : ℝ, 1 ≤ c₁ ∧
    ∀ t : ℕ, Real.log (m t) ≤ c₁ * t * Real.log (t + 2) := by
  -- Let $N$ be a number such that for all $i \geq N$, $p1(i) \leq (i + 2)^2$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ≥ N, (p1 i : ℝ) ≤ (i + 2) ^ 2 := by
    exact Filter.eventually_atTop.mp ( p1_poly_bound ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun i hi => mod_cast hN i hi ⟩;
  -- Let $S = \sum_{i=0}^{N-1} \log(p1(i))$.
  set S := ∑ i ∈ Finset.range N, Real.log (p1 i) with hS_def
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| p1_spec _ |>.1;
  -- We'll use that $Real.log (m t) \leq S + 2 * t * Real.log (t + 2)$ for all $t$.
  have h_log_m_le : ∀ t : ℕ, Real.log (m t) ≤ S + 2 * t * Real.log (t + 2) := by
    intro t
    have h_log_m_le_step : ∀ i < t, Real.log (p1 i) ≤ 2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0) := by
      intro i hi
      split_ifs with hiN
      · have hlog : 0 ≤ Real.log ((t : ℝ) + 2) :=
          Real.log_nonneg (by
            have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
            linarith)
        linarith
      · simp only [add_zero]
        have hNi : N ≤ i := Nat.le_of_not_gt hiN
        have hp_pos : (0 : ℝ) < p1 i := by
          exact_mod_cast (p1_spec i).1.pos
        calc
          Real.log (p1 i) ≤ Real.log (((i : ℝ) + 2) ^ 2) :=
            Real.log_le_log hp_pos (hN i hNi)
          _ = 2 * Real.log ((i : ℝ) + 2) := by
            rw [Real.log_pow]
            norm_num
          _ ≤ 2 * Real.log ((t : ℝ) + 2) := by
            gcongr
    have h_log_m_le_step : Real.log (m t) ≤ ∑ i ∈ Finset.range t, (2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0)) := by
      convert! Finset.sum_le_sum fun i hi => h_log_m_le_step i ( Finset.mem_range.mp hi ) using 1;
      rw [ ← Real.log_prod ] <;> norm_cast ; norm_num [ m ];
      exact fun i hi => Nat.Prime.ne_zero ( p1_spec i |>.1 );
    have h_initial :
        ∑ i ∈ Finset.range t, (if i < N then Real.log (p1 i) else 0) ≤ S := by
      rw [hS_def]
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact hi.2
      · intro i hiN hi
        exact Real.log_nonneg (by
          exact_mod_cast (p1_spec i).1.one_le)
    calc
      Real.log (m t) ≤
          ∑ i ∈ Finset.range t,
            (2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0)) :=
        h_log_m_le_step
      _ = 2 * (t : ℝ) * Real.log (t + 2) +
          ∑ i ∈ Finset.range t, (if i < N then Real.log (p1 i) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
      _ ≤ S + 2 * t * Real.log (t + 2) := by
        linarith
  refine' ⟨ Max.max 1 ( 2 + S / Real.log 3 ), _, _ ⟩ <;> norm_num;
  intro t; specialize h_log_m_le t; rcases eq_or_ne t 0 <;> simp_all +decide [ mul_assoc ] ;
  · unfold m; norm_num;
  · rw [ max_def ] ; split_ifs <;> nlinarith [ show ( t : ℝ ) * Real.log ( t + 2 ) ≥ Real.log 3 by exact le_trans ( Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Nat.pos_of_ne_zero ‹_› ] ) ) ( le_mul_of_one_le_left ( Real.log_nonneg ( by linarith ) ) ( mod_cast Nat.one_le_iff_ne_zero.mpr ‹_› ) ), Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ ( ∑ i ∈ Finset.range N, Real.log ( p1 i ) ) ( ne_of_gt ( Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ) ) ] ;

end Erdos
