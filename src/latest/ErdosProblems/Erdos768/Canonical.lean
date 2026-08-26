import ErdosProblems.Erdos768.Compression

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — the canonical compression fiber bound (Proposition 8.5)

This file assembles the canonical-compression *fiber bound* from the fixed-prefix
fiber bound (`Erdos768Comp.fixed_prefix_card_le`) and the one-prime compression
lemma, packaging everything (together with the squarefreeness / divisibility /
`ω(Q)` facts and the weighted-prefix bound already proved in
`ErdosProblems.Erdos768.Compression`) into `Erdos768.canonical_compression_exists`.
-/

open scoped Classical BigOperators
open Finset Filter

namespace Erdos768Comp

open Erdos768

/-! ### Elementary numerical bounds -/

/-
The number of distinct prime factors is at most `log₂`.
-/
theorem omegaCount_le_log2 (m : ℕ) : omegaCount m ≤ Nat.log 2 m := by
  by_cases hm : m = 0;
  · aesop;
  · exact Nat.le_log_of_pow_le ( by decide ) ( by exact le_trans ( by simpa using! Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) <| Nat.le_of_dvd ( Nat.pos_of_ne_zero hm ) <| Nat.prod_primeFactors_dvd m )

/-- `H_t ≥ 3`. -/
theorem three_le_Ht (t : ℕ) : 3 ≤ Ht t := by
  unfold Ht; omega

/-
`H_t` dominates `log(t+2)/(2 log 2)`.
-/
theorem val_le_Ht (t : ℕ) : Real.log (t + 2) / (2 * Real.log 2) ≤ (Ht t : ℝ) := by
  exact le_trans ( Nat.le_ceil _ ) ( by simp +decide [ Ht ] )

/-- `s_r` is monotone in `r`. -/
theorem sr_mono {r r' : ℕ} (h : r ≤ r') : sr r ≤ sr r' := by
  unfold sr; exact Nat.add_le_add_left (Nat.log_mono_right h) 1

/-
`h_r ≤ H_t` for `r ≤ t`.
-/
theorem hr_le_Ht {r t : ℕ} (h : r ≤ t) : hr r ≤ Ht t := by
  by_cases ht : t ≤ 1;
  · interval_cases t <;> interval_cases r <;> norm_num [ hr, sr, Ht ];
  · refine Nat.div_le_of_le_mul ?_;
    unfold sr Ht;
    -- We'll use that $Nat.log 2 t \leq Real.log (t + 2) / Real.log 2$.
    have h_log : (Nat.log 2 t : ℝ) ≤ Real.log (t + 2) / Real.log 2 := by
      rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Nat.pow_log_le_self 2 ( by linarith : t ≠ 0 ) ] ) ;
    rw [ show ( Real.log ( t + 2 ) / ( 2 * Real.log 2 ) ) = ( Real.log ( t + 2 ) / Real.log 2 ) / 2 by ring ];
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( Real.log ( t + 2 ) / Real.log 2 / 2 ), show ( Nat.log 2 r : ℝ ) ≤ Nat.log 2 t from mod_cast Nat.log_mono_right h ] ;

/-
Real bound on `s_r`: `s_r ≤ (3/(2 log 2)) · log(t+2)` for `2 ≤ r ≤ t`.
-/
theorem sr_le_Lt {r t : ℕ} (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    (sr r : ℝ) ≤ (3 / (2 * Real.log 2)) * Real.log (t + 2) := by
  -- Use the bounds on `Nat.log` and `Real.log`.
  have h_log_bound : (Nat.log 2 r : ℝ) ≤ Real.log r / Real.log 2 ∧ Real.log r ≤ Real.log (t + 2) := by
    exact ⟨ by rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] ; erw [ ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self _ <| by linarith ), Real.log_le_log ( by positivity ) <| by norm_cast; linarith ⟩;
  rw [ div_mul_eq_mul_div, le_div_iff₀ ];
  · rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ] at h_log_bound;
    unfold sr; norm_num; nlinarith [ show ( Real.log 2 :ℝ ) > 0 by positivity, show ( Real.log 4 :ℝ ) = 2 * Real.log 2 by rw [ ← Real.log_rpow ] <;> norm_num, Real.log_le_log ( by norm_num ) ( show ( t:ℝ ) + 2 ≥ 4 by norm_cast; linarith ) ] ;
  · positivity

/-
`1 + log₂⌊x⌋ ≤ (log(3x))²`, i.e. `≤ exp(2 · log log(3x))`.
-/
theorem one_add_log2_le (x : ℝ) (hx : 3 ≤ x) :
    (1 + Nat.log 2 ⌊x⌋₊ : ℝ) ≤ Real.exp (2 * Real.log (Real.log (3 * x))) := by
  rw [ two_mul, Real.exp_add, Real.exp_log ( Real.log_pos <| by linarith ) ];
  -- From Fact 2, we have `Nat.log 2 ⌊x⌋₊ ≤ Real.log x / Real.log 2`. So `1 + Nat.log 2 ⌊x⌋₊ ≤ 1 + Real.log x / Real.log 2`.
  have h_bound : 1 + Nat.log 2 ⌊x⌋₊ ≤ 1 + Real.log x / Real.log 2 := by
    gcongr;
    rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( by exact le_trans ( mod_cast Nat.pow_log_le_self _ <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity ) ;
  -- We'll use that $Real.log (3 * x) ≥ 2$ since $x ≥ 3$.
  have h_log_ge_two : 2 ≤ Real.log (3 * x) := by
    rw [ Real.le_log_iff_exp_le ( by positivity ) ];
    have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 2 : ℝ ) = 1 + 1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ] at *;
  have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 3 : ℝ ) ≥ 2 ), mul_div_cancel₀ ( Real.log x ) ( ne_of_gt ( Real.log_pos one_lt_two ) ) ]

/-
`log log(3x) ≥ 0` for `x ≥ 3`.
-/
theorem LL_nonneg (x : ℝ) (hx : 3 ≤ x) : 0 ≤ Real.log (Real.log (3 * x)) := by
  exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) )

/-
`log(t+2) ≥ 1` for `t ≥ 2`.
-/
theorem one_le_Lt (t : ℕ) (ht : 2 ≤ t) : 1 ≤ Real.log (t + 2) := by
  exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by linarith [ Real.exp_one_lt_d9.le, show ( t : ℝ ) ≥ 2 by norm_cast ] )

/-
The non-`τ(m)` part of the fixed-prefix combinatorial bound is at most
`exp(100·((log(t+2))² + log(t+2)·log log(3x)))`.
-/
theorem comb_G_le (x : ℝ) (hx : 3 ≤ x) (t r m : ℕ) (hr2 : 2 ≤ r) (hrt : r ≤ t)
    (hm : m ≤ ⌊x⌋₊) :
    ((2 : ℝ) ^ (hr r) * ((1 + omegaCount m : ℕ) : ℝ) ^ (sr r) * 2 ^ (hr r * sr r)
        * ((1 + Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ^ (hr r))
      ≤ Real.exp (100 * ((Real.log (t + 2)) ^ 2
          + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  -- Applying the properties of logarithms and exponentials, we can simplify the inequality.
  have h_simplified : Real.log (2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r)) ≤ 100 * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x))) := by
    -- Applying the properties of logarithms and exponentials, we can simplify the inequality to:
    have h_simplified : (hr r : ℝ) * Real.log 2 + (sr r : ℝ) * Real.log (1 + omegaCount m) + (hr r * sr r : ℝ) * Real.log 2 + (hr r : ℝ) * Real.log (1 + Nat.log 2 ⌊x⌋₊) ≤ 100 * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x))) := by
      have hlog2 : Real.log 2 ≤ 1 := by
        exact Real.log_two_lt_d9.le.trans <| by norm_num;
      have hlogx : Real.log (1 + Nat.log 2 ⌊x⌋₊) ≤ 2 * Real.log (Real.log (3 * x)) := by
        convert! Real.log_le_log ?_ ( one_add_log2_le x hx ) using 1;
        · norm_num;
        · positivity
      have hlogm : Real.log (1 + omegaCount m) ≤ 2 * Real.log (Real.log (3 * x)) := by
        refine' le_trans _ hlogx;
        gcongr;
        exact le_trans ( omegaCount_le_log2 m ) ( Nat.log_mono_right hm )
      have hS : (sr r : ℝ) ≤ (3 / (2 * Real.log 2)) * Real.log (t + 2) := by
        convert! sr_le_Lt hr2 hrt using 1
      have hHS : (hr r : ℝ) ≤ (sr r : ℝ) := by
        exact_mod_cast Nat.div_le_self _ _
      have hLt : 1 ≤ Real.log (t + 2) := by
        exact one_le_Lt t ( by linarith )
      have hLL : 0 ≤ Real.log (Real.log (3 * x)) := by
        exact Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
      -- Let $c = \frac{3}{2 \log 2}$, so $c > 0$.
      set c : ℝ := 3 / (2 * Real.log 2)
      have hc_pos : 0 < c := by
        positivity;
      -- Substitute $c$ into the inequality.
      have h_subst : (hr r : ℝ) * Real.log 2 + (sr r : ℝ) * (2 * Real.log (Real.log (3 * x))) + (hr r * sr r : ℝ) * Real.log 2 + (hr r : ℝ) * (2 * Real.log (Real.log (3 * x))) ≤ (c + c^2) * (Real.log (t + 2))^2 + 4 * c * Real.log (t + 2) * Real.log (Real.log (3 * x)) := by
        nlinarith [ mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ ( hr r : ℝ ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ ( sr r : ℝ ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ c * Real.log ( t + 2 ) by positivity ), mul_le_mul_of_nonneg_left hlog2 ( show 0 ≤ c ^ 2 * Real.log ( t + 2 ) ^ 2 by positivity ) ];
      -- We'll use that $c \approx 2.16$ to bound the terms.
      have hc_approx : c < 2.2 := by
        rw [ div_lt_iff₀ ] <;> have := Real.log_two_gt_d9 <;> norm_num at * <;> linarith;
      nlinarith [ mul_le_mul_of_nonneg_left hc_approx.le ( sq_nonneg ( Real.log ( t + 2 ) ) ), mul_le_mul_of_nonneg_left hc_approx.le ( mul_nonneg ( Real.log_nonneg ( show ( t:ℝ ) + 2 ≥ 1 by linarith ) ) hLL ) ];
    convert! h_simplified using 1 ; rw [ Real.log_mul, Real.log_mul, Real.log_mul ] <;> first | positivity | norm_num;
  exact le_trans ( by rw [ Real.exp_log ( by positivity ) ] ; norm_cast ) ( Real.exp_le_exp.mpr h_simplified )

/-! ### The fixed-prefix fiber, exponential form -/

/-
**Fixed-prefix fiber bound, exponential form.**  There is an absolute
constant `C` such that, uniformly for `3 ≤ x`, `2 ≤ r ≤ t`, and every `m`, the
fixed-prefix fiber has size at most
`τ(m)^{H_t} · exp(C·((log(t+2))² + log(t+2)·log log(3x)))`.
-/
theorem fixed_prefix_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t r m : ℕ, 2 ≤ r → r ≤ t →
      ((fixedFiber x t r m).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (C * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  refine' ⟨ 100, by norm_num, fun x hx t r m hr2 hrt => _ ⟩;
  by_cases h : ( fixedFiber x t r m ).Nonempty;
  · obtain ⟨ n₀, hn₀ ⟩ := h;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( comb_G_le x hx t r m hr2 hrt _ ) _ );
    · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( mod_cast Nat.one_le_iff_ne_zero.mpr <| _ ) <| hr_le_Ht hrt ) <| by positivity );
      · convert! fixed_prefix_card_le x t r m hx hr2 hrt using 1;
        norm_cast ; ring_nf;
      · exact ne_of_gt <| Finset.card_pos.mpr ⟨ 1, Nat.one_mem_divisors.mpr <| by
          intro h; simp_all +decide [ fixedFiber ] ;
          exact absurd ( hn₀.2.2.2.resolve_left ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Nat.pos_of_ne_zero ( by exact fun h => by have := Qr_dvd n₀ r ( by linarith ) ( by linarith ) ( by linarith ) ; aesop ) ) ) ) ) ) ) ) ) ) ( not_lt_of_ge ( Nat.le_of_dvd ( by linarith ) ( Qr_dvd n₀ r ( by linarith ) ( by linarith ) ( by linarith ) ) ) ) ⟩;
    · unfold fixedFiber at hn₀;
      norm_num +zetaDelta at *;
      exact hn₀.2.2.2 ▸ Nat.div_le_self _ _ |> le_trans <| hn₀.1.2;
    · positivity;
  · rw [ Finset.not_nonempty_iff_eq_empty.mp h ] ; norm_num ; positivity

/-! ### The one-prime compression fiber -/

/-
For `ω(n) ≥ 1`, the largest prime factor `pnth n 1` is a genuine prime factor.
-/
theorem pnth1_mem (n : ℕ) (h : 1 ≤ omegaCount n) : pnth n 1 ∈ n.primeFactors := by
  unfold pnth; simp +decide [ omegaCount ] at h ⊢;
  rcases x : n.primeFactors.sort ( fun x1 x2 => x2 ≤ x1 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
  · replace x := congr_arg List.length x ; aesop;
  · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;
  · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;

/-- The one-prime fiber: `n ≤ x` in `𝒜` with `ω(n) = t` and `n / P⁺(n) = m`. -/
noncomputable def oneprimeSet (x : ℝ) (t m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / pnth n 1 = m)

/-- **One-prime compression (Lemma 8.6).**  `#(oneprimeSet x t m) ≤ τ(m)·(1+⌊log₂ x⌋)`. -/
theorem oneprime_card_le (x : ℝ) (t m : ℕ) (ht : 2 ≤ t) :
    (oneprimeSet x t m).card ≤ tauCount m * (1 + Nat.log 2 ⌊x⌋₊) := by
  set f : ℕ → ℕ × ℕ := fun n => (Dwit n (pnth n 1), List.idxOf (pnth n 1) ((Dwit n (pnth n 1) - 1).primeFactors.sort (· ≤ ·))) with hf_def;
  have h_mapsTo : ∀ n ∈ oneprimeSet x t m, f n ∈ m.divisors ×ˢ Finset.range (1 + Nat.log 2 ⌊x⌋₊) := by
    intro n hn
    simp [f] at *;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · have h_coprime : Nat.Coprime (Dwit n (pnth n 1)) (pnth n 1) := by
        apply Nat.Coprime.symm; exact (by
          have := Dwit_not_dvd n (pnth n 1) (by
          exact Finset.mem_filter.mp hn |>.2.1) (by
          exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
          exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
          exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))
          exact Nat.Prime.coprime_iff_not_dvd ( by
            exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) ) ) |>.2 this);
      have h_div : Dwit n (pnth n 1) ∣ n := by
        apply (Dwit_spec n (pnth n 1) (by
        exact Finset.mem_filter.mp hn |>.2.1) (by
        exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) )) (by
        exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) )) (by
        unfold oneprimeSet at hn; aesop;)).left;
      have h_div_m : Dwit n (pnth n 1) ∣ m * pnth n 1 := by
        convert! h_div using 1;
        rw [ ← Finset.mem_filter.mp hn |>.2.2.2, Nat.div_mul_cancel ];
        exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) );
      exact h_coprime.dvd_of_dvd_mul_right h_div_m;
    · intro hm; simp_all +decide [ oneprimeSet ] ;
      have := pnth1_mem n ( by linarith ) ; simp_all +decide ;
      exact hn.2.2.2.elim ( fun h => by aesop ) fun h => by linarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero this.2.2 ) this.2.1 ] ;
    · refine' lt_of_lt_of_le ( List.idxOf_lt_length_iff.mpr _ ) _;
      · have := Dwit_spec n ( pnth n 1 ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
        · have := pnth1_mem n ?_ <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          · exact ⟨ by rw [ ← Nat.mod_add_div ( Dwit n ( pnth n 1 ) ) ( pnth n 1 ), ‹n % Dwit n ( pnth n 1 ) = 0 ∧ 1 < Dwit n ( pnth n 1 ) ∧ Dwit n ( pnth n 1 ) % pnth n 1 = 1›.2.2 ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt this.1.one_lt ], Nat.sub_ne_zero_of_lt <| by linarith ⟩;
          · contrapose! this; interval_cases n <;> simp_all +decide ;
        · exact Finset.mem_filter.mp hn |>.2.1;
        · exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ) );
        · exact Nat.mod_eq_zero_of_dvd <| Nat.dvd_of_mem_primeFactors <| pnth1_mem n <| by linarith [ Finset.mem_filter.mp hn |>.2.2.1 ] ;
        · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 );
      · have h_Dwit_le_floor : Dwit n (pnth n 1) - 1 ≤ ⌊x⌋₊ := by
          have h_Dwit_le_floor : Dwit n (pnth n 1) ≤ n := by
            have h_Dwit_le_n : Dwit n (pnth n 1) ∣ n := by
              apply (Dwit_spec n (pnth n 1) (by
              exact Finset.mem_filter.mp hn |>.2.1) (by
              exact Nat.prime_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
              exact Nat.dvd_of_mem_primeFactors ( pnth1_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) )) (by
              exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))).left;
            apply Nat.le_of_dvd (Nat.pos_of_ne_zero (by
            exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ))) h_Dwit_le_n;
          exact Nat.sub_le_of_le_add <| by linarith [ show n ≤ ⌊x⌋₊ from Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ] ;
        have h_prime_factors_card : (Dwit n (pnth n 1) - 1).primeFactors.card ≤ Nat.log 2 (Dwit n (pnth n 1) - 1) := by
          exact omegaCount_le_log2 _;
        simp +zetaDelta at *;
        exact le_trans h_prime_factors_card ( Nat.le_trans ( Nat.log_mono_right <| Nat.sub_le_sub_right h_Dwit_le_floor 1 ) <| by simp +arith +decide );
  have h_injOn : ∀ n n' : ℕ, n ∈ oneprimeSet x t m → n' ∈ oneprimeSet x t m → f n = f n' → n = n' := by
    intros n n' hn hn' h_eq
    have hp_mem : ∀ k ∈ oneprimeSet x t m, pnth k 1 ∈ k.primeFactors := by
      intro k hk; exact pnth1_mem k (by grind +locals)
    have hp_dvd : ∀ k ∈ oneprimeSet x t m, pnth k 1 ∣ Dwit k (pnth k 1) - 1 := by
      intro k hk
      have hpk := hp_mem k hk
      have hspec := Dwit_spec k (pnth k 1) (Finset.mem_filter.mp hk |>.2.1)
        (Nat.prime_of_mem_primeFactors hpk) (Nat.dvd_of_mem_primeFactors hpk)
        (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hk |>.1) |>.1))
      exact Nat.dvd_of_mod_eq_zero (by
        rw [← Nat.mod_add_div (Dwit k (pnth k 1)) (pnth k 1), hspec.2.2]
        norm_num [Nat.mod_eq_of_lt (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hpk))])
    have hDpos : ∀ k ∈ oneprimeSet x t m, 1 < Dwit k (pnth k 1) := by
      intro k hk
      have hpk := hp_mem k hk
      exact (Dwit_spec k (pnth k 1) (Finset.mem_filter.mp hk |>.2.1)
        (Nat.prime_of_mem_primeFactors hpk) (Nat.dvd_of_mem_primeFactors hpk)
        (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hk |>.1) |>.1))).2.1
    have hmemL : ∀ k ∈ oneprimeSet x t m,
        pnth k 1 ∈ (Dwit k (pnth k 1) - 1).primeFactors.sort (· ≤ ·) := by
      intro k hk
      rw [Finset.mem_sort]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (hp_mem k hk),
        hp_dvd k hk, Nat.sub_ne_zero_of_lt (hDpos k hk)⟩
    have hDeq : Dwit n (pnth n 1) = Dwit n' (pnth n' 1) := congrArg Prod.fst h_eq
    have hsnd := congrArg Prod.snd h_eq
    simp only [f] at hsnd
    rw [hDeq] at hsnd
    have hmem := hmemL n hn
    rw [hDeq] at hmem
    have hp_eq : pnth n 1 = pnth n' 1 := (List.idxOf_inj hmem).mp hsnd
    have h_n : n = m * pnth n 1 := by
      rw [← Finset.mem_filter.mp hn |>.2.2.2, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (hp_mem n hn))]
    have h_n' : n' = m * pnth n' 1 := by
      rw [← Finset.mem_filter.mp hn' |>.2.2.2, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (hp_mem n' hn'))]
    rw [h_n, h_n', hp_eq]
  calc (oneprimeSet x t m).card
      = (Finset.image f (oneprimeSet x t m)).card :=
        (Finset.card_image_of_injOn (fun n hn n' hn' h => h_injOn n n' hn hn' h)).symm
    _ ≤ (m.divisors ×ˢ Finset.range (1 + Nat.log 2 ⌊x⌋₊)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr h_mapsTo)
    _ = tauCount m * (1 + Nat.log 2 ⌊x⌋₊) := by
        rw [Finset.card_product, Finset.card_range]

/-
**One-prime fiber bound, exponential form.**
-/
theorem oneprime_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t m : ℕ, 2 ≤ t →
      ((oneprimeSet x t m).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (C * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  refine' ⟨ 2, by norm_num, _ ⟩;
  intros x hx t m ht
  by_cases htau : tauCount m = 0;
  · by_cases hm : m = 0 <;> simp_all +decide [ tauCount ];
    rw [ Finset.card_eq_zero.mpr ] <;> norm_num [ oneprimeSet ];
    · positivity;
    · intro n hn₁ hn₂ hn₃ hn₄; exact ⟨ Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| pnth1_mem n <| by linarith, Nat.le_of_dvd hn₁ <| Nat.dvd_of_mem_primeFactors <| pnth1_mem n <| by linarith ⟩ ;
  · -- Applying the bounds from `oneprime_card_le` and `one_add_log2_le`.
    have h_bound : (oneprimeSet x t m).card ≤ (tauCount m : ℝ) * Real.exp (2 * Real.log (Real.log (3 * x))) := by
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( one_add_log2_le x hx ) <| Nat.cast_nonneg _ );
      exact_mod_cast oneprime_card_le x t m ht;
    refine le_trans h_bound ?_;
    gcongr;
    · exact_mod_cast Nat.le_self_pow ( by linarith [ three_le_Ht t ] ) _;
    · nlinarith only [ show 1 ≤ Real.log ( t + 2 ) from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( t : ℝ ) ≥ 2 by norm_cast ] ), show 0 ≤ Real.log ( Real.log ( 3 * x ) ) from Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( x : ℝ ) ≥ 3 by norm_cast ] ]

/-! ### The canonical fiber bound -/

/-
**Canonical compression fiber (Proposition 8.5).**
-/
theorem canonical_fiber_bound :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∀ (x : ℝ), 3 ≤ x → ∀ t : ℕ, 2 ≤ t → ∀ m : ℕ,
      (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qcanon n = m)).card : ℝ)
        ≤ (tauCount m : ℝ) ^ (Ht t) *
            Real.exp (Cfib * ((Real.log (t + 2)) ^ 2
              + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
  obtain ⟨C₁, hC₁pos, hfix⟩ := fixed_prefix_exp
  obtain ⟨C₂, hC₂pos, hone⟩ := oneprime_exp
  set Cfib := max C₁ C₂ + 1
  have hCfibpos : 0 < Cfib := by
    positivity
  use Cfib;
  refine' ⟨ hCfibpos, fun x hx t ht m => _ ⟩;
  -- Let `F := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qcanon n = m)` (this is the goal's set).
  set F := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qcanon n = m);
  -- Let `Fr := F.filter (fun n => rhoIdx n = r)`.
  have hFfib : ∀ r ∈ Finset.Icc 1 t, ((F.filter (fun n => rhoIdx n = r)).card : ℝ) ≤ (tauCount m : ℝ) ^ (Ht t) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    intro r hr; by_cases hr1 : r = 1 <;> simp_all +decide ;
    · refine' le_trans _ ( le_trans ( hone x hx t m ht ) _ );
      · refine' mod_cast Finset.card_le_card _;
        simp +contextual [ Finset.subset_iff, oneprimeSet ];
        simp +zetaDelta at *;
        unfold Qcanon; aesop;
      · gcongr;
        · exact add_nonneg ( sq_nonneg _ ) ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) );
        · exact le_max_right _ _;
    · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| add_nonneg ( sq_nonneg _ ) <| mul_nonneg ( Real.log_nonneg <| by norm_cast; linarith ) <| Real.log_nonneg <| _ ) <| by positivity );
      · refine' le_trans _ ( hfix x hx t r m ( Nat.lt_of_le_of_ne hr.1 ( Ne.symm hr1 ) ) hr.2 );
        refine' mod_cast Finset.card_le_card _;
        simp +contextual [ Finset.subset_iff, fixedFiber ];
        simp +zetaDelta at *;
        unfold Qcanon; aesop;
      · exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) );
  -- By summing over all `r` in `Finset.Icc 1 t`, we get the desired inequality.
  have hFfib_sum : ((F).card : ℝ) ≤ (t : ℝ) * (tauCount m : ℝ) ^ (Ht t) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    have hFfib_sum : ((F).card : ℝ) = ∑ r ∈ Finset.Icc 1 t, ((F.filter (fun n => rhoIdx n = r)).card : ℝ) := by
      rw_mod_cast [ ← Finset.card_biUnion ];
      · congr with n ; simp +decide;
        intro hn; have := rhoIdx_mem n ( by linarith [ Finset.mem_filter.mp hn ] ) ; aesop;
      · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
    exact hFfib_sum.symm ▸ le_trans ( Finset.sum_le_sum hFfib ) ( by norm_num; linarith );
  -- Since $t \leq \exp(\log(t+2))$, we can bound the right-hand side.
  have h_bound : (t : ℝ) * Real.exp (max C₁ C₂ * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) ≤ Real.exp ((max C₁ C₂ + 1) * ((Real.log (t + 2)) ^ 2 + Real.log (t + 2) * Real.log (Real.log (3 * x)))) := by
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_exp ];
    nlinarith only [ show Real.log t ≤ Real.log ( t + 2 ) by exact Real.log_le_log ( by positivity ) ( by linarith ), show Real.log ( t + 2 ) ≥ 1 by exact Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( t : ℝ ) ≥ 2 by norm_cast ], show 0 ≤ Real.log ( Real.log ( 3 * x ) ) by exact Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith, show 0 ≤ max C₁ C₂ by positivity ];
  exact hFfib_sum.trans ( by convert! mul_le_mul_of_nonneg_left h_bound ( by positivity : 0 ≤ ( tauCount m : ℝ ) ^ Ht t ) using 1 ; ring )

/-
`ω(Q(n)) ≤ H_{ω(n)}` for `n ∈ 𝒜` with `ω(n) ≥ 2`.
-/
theorem omega_Qcanon_le (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    omegaCount (Qcanon n) ≤ Ht (omegaCount n) := by
  by_cases h : rhoIdx n = 1;
  · -- Since `rhoIdx n = 1`, we have `Qcanon n = pnth n 1`.
    have hQcanon : Qcanon n = pnth n 1 := by
      unfold Qcanon; aesop;
    -- Since `pnth n 1` is a prime factor of `n`, we have `omegaCount (pnth n 1) ≤ 1`.
    have homegaCount_pnth : omegaCount (pnth n 1) ≤ 1 := by
      unfold pnth omegaCount;
      rcases x : n.primeFactors.sort ( fun x1 x2 => x1 ≥ x2 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
      · replace x := congr_arg List.length x; simp_all +decide ;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x a; aesop;
    exact hQcanon ▸ homegaCount_pnth.trans ( by linarith [ three_le_Ht ( omegaCount n ) ] );
  · rw [ show Qcanon n = Qr n ( rhoIdx n ) from ?_ ];
    · rw [ Qr_omega ];
      · exact hr_le_Ht ( rhoIdx_mem n ( by linarith ) |> Finset.mem_Icc.mp |> And.right );
      · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
      · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2;
    · exact if_neg h

end Erdos768Comp
